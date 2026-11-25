/*
 * smith_fast.c — P-smooth tree generalization of Robert Smith's Euler/Hutton
 * BBP-style extraction with 32-bit Barrett reduction and 96-bit certified fixed point,
 * with 64-bit Montgomery fallback for tree moduli in [2^31, 2^61) and pthreads.
 *
 * Computes the certified binary window of {2^(n-1) * pi} (matching bellard_bench).
 *
 * Modes:
 *   smith3m   : exact Robert Smith M/3M pairing
 *   smooth    : P-smooth tree with parameter P in {1, 3, 5, 7, 11, 13, 17, 19, 23}
 *
 * Compile:
 *   cc -O3 -pthread -o smith_fast smith_fast.c
 *
 * Usage:
 *   ./smith_fast <smith3m|smooth> <n> [P=19] [width=32] [threads=1]
 */

#define _DARWIN_C_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

typedef unsigned __int128 u128;

enum { PRECISION = 96 };
#define FIXED_MASK (((u128)1 << PRECISION) - 1)

static const uint64_t ODD_PRIMES[] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31};
#define MAX_P_IDX 10
static const uint64_t MOD32_CAP = (1ULL << 31);
static const uint64_t MOD64_CAP = (1ULL << 61);

static double wall_time(void) {
    struct timespec now;
#ifdef __APPLE__
    clock_gettime(CLOCK_UPTIME_RAW, &now);
#else
    clock_gettime(CLOCK_MONOTONIC, &now);
#endif
    return (double)now.tv_sec + (double)now.tv_nsec * 1e-9;
}

/* ==================== 32-bit Barrett reduction ==================== */

typedef struct {
    uint64_t reciprocal;
    uint32_t q;
} Mod32;

static inline Mod32 mod32_init(uint32_t q) {
    return (Mod32){UINT64_MAX / q, q};
}

static inline uint32_t mod32_reduce(uint64_t z, Mod32 m) {
    uint64_t quotient = ((u128)z * m.reciprocal) >> 64;
    uint64_t r = z - quotient * m.q;
    return r >= m.q ? r - m.q : r;
}

static inline uint32_t mod32_mul(uint32_t a, uint32_t b, Mod32 m) {
    return mod32_reduce((uint64_t)a * b, m);
}

static inline uint32_t mod32_add(uint32_t a, uint32_t b, uint32_t q) {
    uint32_t s = a + b;
    return s >= q ? s - q : s;
}

static inline uint32_t mod32_sub(uint32_t a, uint32_t b, uint32_t q) {
    return a >= b ? a - b : a + q - b;
}

static inline uint32_t mod32_neg(uint32_t a, uint32_t q) {
    return a ? q - a : 0;
}

static inline uint32_t mod32_dbl(uint32_t a, uint32_t q) {
    return mod32_add(a, a, q);
}

static inline uint32_t mod32_halve(uint32_t a, uint32_t q) {
    return (a & 1) ? (uint32_t)(((uint64_t)a + q) >> 1) : (a >> 1);
}

static inline uint32_t mod32_halve_k(uint32_t a, uint32_t q, int k) {
    for (int i = 0; i < k; i++) a = mod32_halve(a, q);
    return a;
}

static inline uint32_t mod32_pow2(uint64_t e, Mod32 m) {
    int remaining = (e < 64) ? 0 : (58 - __builtin_clzll(e));
    uint64_t r = mod32_reduce(UINT64_C(1) << (e >> remaining), m);
    while (remaining) {
        --remaining;
        r = mod32_reduce((r * r) << ((e >> remaining) & 1), m);
    }
    return (uint32_t)r;
}

/* Modular inverse of a mod q (q odd, gcd(a,q)=1) via extended Euclidean (fast on ARM64 udiv) */
static inline uint32_t mod32_inv(uint32_t a, uint32_t q) {
    int64_t t = 0, newt = 1;
    int64_t r = (int64_t)q, newr = (int64_t)a;
    while (newr != 0) {
        int64_t quot = r / newr;
        int64_t tmp = t - quot * newt; t = newt; newt = tmp;
        tmp = r - quot * newr; r = newr; newr = tmp;
    }
    if (t < 0) t += q;
    return (uint32_t)t;
}

static inline uint32_t mod32_pow_small(uint32_t w, uint64_t p, Mod32 m) {
    uint32_t w2 = mod32_mul(w, w, m);
    switch (p) {
        case 3:  return mod32_mul(w2, w, m);
        case 5:  { uint32_t w4 = mod32_mul(w2, w2, m); return mod32_mul(w4, w, m); }
        case 7:  { uint32_t w3 = mod32_mul(w2, w, m); uint32_t w4 = mod32_mul(w2, w2, m); return mod32_mul(w4, w3, m); }
        case 11: { uint32_t w3 = mod32_mul(w2, w, m); uint32_t w4 = mod32_mul(w2, w2, m); uint32_t w8 = mod32_mul(w4, w4, m); return mod32_mul(w8, w3, m); }
        case 13: { uint32_t w4 = mod32_mul(w2, w2, m); uint32_t w5 = mod32_mul(w4, w, m); uint32_t w8 = mod32_mul(w4, w4, m); return mod32_mul(w8, w5, m); }
        default: {
            uint32_t r = 1, b = w;
            while (p) {
                if (p & 1) r = mod32_mul(r, b, m);
                p >>= 1;
                if (p) b = mod32_mul(b, b, m);
            }
            return r;
        }
    }
}

/* Exact 96-bit fixed-point fraction floor(r * 2^96 / q) for 32-bit q */
static inline u128 fixed_fraction32(uint32_t r, uint32_t q) {
    uint64_t z = (uint64_t)r << 32;
    uint64_t a = z / q;
    z = (z - a * q) << 32;
    uint64_t b = z / q;
    z = (z - b * q) << 32;
    return ((u128)a << 64) | (b << 32) | (z / q);
}

/* ==================== 64-bit Montgomery fallback (q in [2^31, 2^61)) ==================== */

typedef struct {
    uint64_t n;
    uint64_t ninv;
    uint64_t one;
    uint64_t r2;
} Mont64;

static inline uint64_t mont64_inv(uint64_t n) {
    uint64_t x = n;
    x *= 2 - n * x;
    x *= 2 - n * x;
    x *= 2 - n * x;
    x *= 2 - n * x;
    x *= 2 - n * x;
    return -x;
}

static inline uint64_t mont64_redc(const Mont64 *m, u128 t) {
    uint64_t q = (uint64_t)t * m->ninv;
    uint64_t r = (uint64_t)((t + (u128)q * m->n) >> 64);
    if (r >= m->n) r -= m->n;
    return r;
}

static inline uint64_t mont64_mul(const Mont64 *m, uint64_t a, uint64_t b) {
    return mont64_redc(m, (u128)a * b);
}

static inline uint64_t mont64_add(const Mont64 *m, uint64_t a, uint64_t b) {
    uint64_t s = a + b;
    return s >= m->n ? s - m->n : s;
}

static inline uint64_t mont64_sub(const Mont64 *m, uint64_t a, uint64_t b) {
    return a >= b ? a - b : a + m->n - b;
}

static inline uint64_t mont64_dbl(const Mont64 *m, uint64_t a) {
    return mont64_add(m, a, a);
}

static inline uint64_t mont64_halve(const Mont64 *m, uint64_t a) {
    return (a & 1) ? ((a + m->n) >> 1) : (a >> 1);
}

static inline uint64_t mont64_halve_k(const Mont64 *m, uint64_t a, int k) {
    for (int i = 0; i < k; i++) a = mont64_halve(m, a);
    return a;
}

static inline void mont64_init(Mont64 *m, uint64_t n) {
    m->n = n;
    m->ninv = mont64_inv(n);
    uint64_t r1 = (uint64_t)((((u128)1) << 64) % n);
    m->one = r1;
    m->r2 = (uint64_t)(((u128)r1 * r1) % n);
}

static inline uint64_t mont64_to(const Mont64 *m, uint64_t x) {
    return mont64_mul(m, x % m->n, m->r2);
}

static inline uint64_t mont64_from(const Mont64 *m, uint64_t a) {
    return mont64_redc(m, (u128)a);
}

static uint64_t mont64_pow2(const Mont64 *m, uint64_t e) {
    if (e == 0) return m->one;
    int bit = 63 - __builtin_clzll(e);
    uint64_t res = m->one;
    for (; bit >= 0; bit--) {
        res = mont64_mul(m, res, res);
        if ((e >> bit) & 1) res = mont64_dbl(m, res);
    }
    return res;
}

static uint64_t mont64_pow_inv2(const Mont64 *m, uint64_t e) {
    if (e == 0) return m->one;
    int bit = 63 - __builtin_clzll(e);
    uint64_t res = m->one;
    for (; bit >= 0; bit--) {
        res = mont64_mul(m, res, res);
        if ((e >> bit) & 1) res = mont64_halve(m, res);
    }
    return res;
}

static inline uint64_t mont64_pow_small(const Mont64 *m, uint64_t w, uint64_t p) {
    uint64_t w2 = mont64_mul(m, w, w);
    switch (p) {
        case 3:  return mont64_mul(m, w2, w);
        case 5:  { uint64_t w4 = mont64_mul(m, w2, w2); return mont64_mul(m, w4, w); }
        case 7:  { uint64_t w3 = mont64_mul(m, w2, w); uint64_t w4 = mont64_mul(m, w2, w2); return mont64_mul(m, w4, w3); }
        case 11: { uint64_t w3 = mont64_mul(m, w2, w); uint64_t w4 = mont64_mul(m, w2, w2); uint64_t w8 = mont64_mul(m, w4, w4); return mont64_mul(m, w8, w3); }
        case 13: { uint64_t w4 = mont64_mul(m, w2, w2); uint64_t w5 = mont64_mul(m, w4, w); uint64_t w8 = mont64_mul(m, w4, w4); return mont64_mul(m, w8, w5); }
        default: {
            uint64_t r = m->one, b = w;
            while (p) {
                if (p & 1) r = mont64_mul(m, r, b);
                p >>= 1;
                if (p) b = mont64_mul(m, b, b);
            }
            return r;
        }
    }
}

/* Exact 96-bit fixed-point fraction floor(r * 2^96 / q) for 64-bit q < 2^61 */
static inline u128 fixed_fraction64(uint64_t r, uint64_t q) {
    /* 3 steps of 32 bits: z = (rem << 32) < 2^93 fits in u128 */
    u128 z = (u128)r << 32;
    uint64_t a = (uint64_t)(z / q);
    z = (z - (u128)a * q) << 32;
    uint64_t b = (uint64_t)(z / q);
    z = (z - (u128)b * q) << 32;
    uint64_t c = (uint64_t)(z / q);
    return ((u128)a << 64) | ((u128)b << 32) | c;
}

/* ==================== Core evaluation ==================== */

typedef struct {
    u128 sum;
    uint64_t rounded;
    uint64_t modexps;
    uint64_t cores32;
    uint64_t cores64;
    uint64_t subroots;
} Partial;

typedef struct {
    int64_t d;
    uint64_t M_max;
    int mode; /* 0 = smith3m, 1 = smooth */
    int P;
    int num_primes;
    uint64_t primes[MAX_P_IDX];
    int prime_half[MAX_P_IDX];
    /* Wheel for odd P-rough cores mod 210 (when P >= 7) or mod 30 (P=5) or mod 6 (P=3) */
    uint64_t wheel_mod;
    uint64_t wheel_res[48];
    int wheel_len;
} Config;

static inline void accum32(Partial *out, uint32_t r, uint32_t q) {
    out->sum += fixed_fraction32(r, q);
    out->rounded++;
}

static inline void accum64(Partial *out, uint64_t r, uint64_t q) {
    out->sum += fixed_fraction64(r, q);
    out->rounded++;
}

/* Evaluate a single standalone modulus M < 2^31 using 32-bit Barrett */
static inline void eval_single32(const Config *cfg, Partial *out, uint32_t M) {
    if (M <= 1) return;
    int64_t d = cfg->d;
    int64_t k = (int64_t)((M - 1) >> 1);
    int64_t e1 = d + 1 - 3 * k;
    if (e1 < 0) return;
    int64_t e2 = d - 1 - 5 * k;

    out->cores32++;
    Mod32 m = mod32_init(M);
    int s12 = ((k >> 1) & 1) ? -1 : 1;

    uint32_t num;
    if (e2 < 0) {
        out->modexps += 1;
        uint32_t r1 = mod32_pow2((uint64_t)e1, m);
        num = (s12 > 0) ? r1 : mod32_neg(r1, M);
    } else {
        /* Step UP from smallest active exponent using x = 2^k mod M (zero modinv!) */
        out->modexps += 2;
        int64_t e3 = d - 1 - 6 * k;
        int64_t e4 = d - 4 - 10 * k;
        int s34 = (k & 1) ? -1 : 1;
        uint32_t x = mod32_pow2((uint64_t)k, m);
        uint32_t x2 = mod32_mul(x, x, m);

        uint32_t r1, r2, r3 = 0, r4 = 0;
        if (e4 >= 0) {
            r4 = mod32_pow2((uint64_t)e4, m);
            uint32_t x4 = mod32_mul(x2, x2, m);
            r3 = mod32_mul(r4, mod32_reduce((uint64_t)x4 << 3, m), m);
            r2 = mod32_mul(r3, x, m);
            r1 = mod32_mul(r2, mod32_reduce((uint64_t)x2 << 2, m), m);
        } else if (e3 >= 0) {
            r3 = mod32_pow2((uint64_t)e3, m);
            r2 = mod32_mul(r3, x, m);
            r1 = mod32_mul(r2, mod32_reduce((uint64_t)x2 << 2, m), m);
        } else {
            r2 = mod32_pow2((uint64_t)e2, m);
            r1 = mod32_mul(r2, mod32_reduce((uint64_t)x2 << 2, m), m);
        }
        uint32_t t12 = mod32_add(r1, r2, M);
        num = (s12 > 0) ? t12 : mod32_neg(t12, M);
        if (e3 >= 0) {
            uint32_t t34 = (e4 >= 0) ? mod32_add(r3, r4, M) : r3;
            num = (s34 > 0) ? mod32_add(num, t34, M) : mod32_sub(num, t34, M);
        }
    }
    accum32(out, num, M);
}

/* Evaluate a single standalone modulus M >= 2^31 using 64-bit Montgomery */
static inline void eval_single64(const Config *cfg, Partial *out, uint64_t M) {
    if (M <= 1) return;
    int64_t d = cfg->d;
    int64_t k = (int64_t)((M - 1) >> 1);
    int64_t e1 = d + 1 - 3 * k;
    if (e1 < 0) return;
    int64_t e2 = d - 1 - 5 * k;

    out->cores64++;
    Mont64 m;
    mont64_init(&m, M);
    int s12 = ((k >> 1) & 1) ? -1 : 1;

    uint64_t num;
    if (e2 < 0) {
        out->modexps += 1;
        uint64_t r1 = mont64_pow2(&m, (uint64_t)e1);
        num = (s12 > 0) ? r1 : (r1 ? M - r1 : 0);
    } else {
        out->modexps += 2;
        int64_t e3 = d - 1 - 6 * k;
        int64_t e4 = d - 4 - 10 * k;
        int s34 = (k & 1) ? -1 : 1;
        uint64_t rd = mont64_pow2(&m, (uint64_t)d);
        uint64_t w = mont64_pow_inv2(&m, (uint64_t)k);
        uint64_t w2 = mont64_mul(&m, w, w);
        uint64_t w3 = mont64_mul(&m, w2, w);
        uint64_t w5 = mont64_mul(&m, w3, w2);
        uint64_t t12 = mont64_add(&m, mont64_dbl(&m, w3), mont64_halve(&m, w5));
        num = (s12 > 0) ? t12 : (t12 ? M - t12 : 0);
        if (e3 >= 0) {
            uint64_t w6 = mont64_mul(&m, w3, w3);
            uint64_t t34 = mont64_halve(&m, w6);
            if (e4 >= 0) {
                uint64_t w10 = mont64_mul(&m, w5, w5);
                t34 = mont64_add(&m, t34, mont64_halve_k(&m, w10, 4));
            }
            num = (s34 > 0) ? mont64_add(&m, num, t34) : mont64_sub(&m, num, t34);
        }
        num = mont64_mul(&m, num, rd);
    }
    accum64(out, mont64_from(&m, num), M);
}

static inline void eval_single(const Config *cfg, Partial *out, uint64_t M) {
    if (M < MOD32_CAP) eval_single32(cfg, out, (uint32_t)M);
    else eval_single64(cfg, out, M);
}

/* Exact Smith M/3M pairing using 32-bit Barrett when 3*M < 2^31 */
static inline void eval_smith_pair3(const Config *cfg, Partial *out, uint64_t M) {
    if (3 * M > cfg->M_max) {
        eval_single(cfg, out, M);
        return;
    }
    uint64_t N_mod = 3 * M;
    int64_t d = cfg->d;
    uint64_t k0 = (M - 1) >> 1;

    if (N_mod < MOD32_CAP) {
        uint32_t q = (uint32_t)N_mod;
        out->cores32++;
        out->modexps += 2;
        Mod32 m = mod32_init(q);

        uint32_t rd = mod32_pow2((uint64_t)d, m);
        uint32_t x0 = mod32_pow2(k0, m);
        uint32_t w0 = mod32_inv(x0, q);
        uint32_t w1 = mod32_halve(mod32_pow_small(w0, 3, m), q);

        uint32_t acc = 0;
        uint64_t Ms[2] = {M, N_mod};
        uint32_t ws[2] = {w0, w1};
        for (int idx = 0; idx < 2; idx++) {
            uint64_t curM = Ms[idx];
            if (curM <= 1) continue;
            int64_t k = (int64_t)((curM - 1) >> 1);
            int64_t e1 = d + 1 - 3 * k;
            if (e1 < 0) continue;
            int64_t e2 = d - 1 - 5 * k;
            int64_t e3 = d - 1 - 6 * k;
            int64_t e4 = d - 4 - 10 * k;
            int s12 = ((k >> 1) & 1) ? -1 : 1;
            int s34 = (k & 1) ? -1 : 1;

            uint32_t w = ws[idx];
            uint32_t w2 = mod32_mul(w, w, m);
            uint32_t w3 = mod32_mul(w2, w, m);
            uint32_t t12 = mod32_dbl(w3, q);
            uint32_t w5 = 0;
            if (e2 >= 0) {
                w5 = mod32_mul(w3, w2, m);
                t12 = mod32_add(t12, mod32_halve(w5, q), q);
            }
            uint32_t num = (s12 > 0) ? t12 : mod32_neg(t12, q);
            if (e3 >= 0) {
                uint32_t w6 = mod32_mul(w3, w3, m);
                uint32_t t34 = mod32_halve(w6, q);
                if (e4 >= 0) {
                    uint32_t w10 = mod32_mul(w5, w5, m);
                    t34 = mod32_add(t34, mod32_halve_k(w10, q, 4), q);
                }
                num = (s34 > 0) ? mod32_add(num, t34, q) : mod32_sub(num, t34, q);
            }
            if (idx == 0) {
                num = mod32_add(num, mod32_dbl(num, q), q);
            }
            acc = mod32_add(acc, num, q);
        }
        uint32_t r = mod32_mul(acc, rd, m);
        accum32(out, r, q);
    } else {
        /* Rare 64-bit fallback (for d > 2e9) */
        out->cores64++;
        out->modexps += 2;
        Mont64 m;
        mont64_init(&m, N_mod);
        uint64_t rd = mont64_pow2(&m, (uint64_t)d);
        uint64_t w0 = mont64_pow_inv2(&m, k0);
        uint64_t w1 = mont64_halve(&m, mont64_pow_small(&m, w0, 3));
        uint64_t acc = 0;
        uint64_t Ms[2] = {M, N_mod};
        uint64_t ws[2] = {w0, w1};
        for (int idx = 0; idx < 2; idx++) {
            uint64_t curM = Ms[idx];
            if (curM <= 1) continue;
            int64_t k = (int64_t)((curM - 1) >> 1);
            int64_t e1 = d + 1 - 3 * k;
            if (e1 < 0) continue;
            int64_t e2 = d - 1 - 5 * k;
            int64_t e3 = d - 1 - 6 * k;
            int64_t e4 = d - 4 - 10 * k;
            int s12 = ((k >> 1) & 1) ? -1 : 1;
            int s34 = (k & 1) ? -1 : 1;
            uint64_t w = ws[idx];
            uint64_t w2 = mont64_mul(&m, w, w);
            uint64_t w3 = mont64_mul(&m, w2, w);
            uint64_t t12 = mont64_dbl(&m, w3);
            uint64_t w5 = 0;
            if (e2 >= 0) {
                w5 = mont64_mul(&m, w3, w2);
                t12 = mont64_add(&m, t12, mont64_halve(&m, w5));
            }
            uint64_t num = (s12 > 0) ? t12 : (t12 ? N_mod - t12 : 0);
            if (e3 >= 0) {
                uint64_t w6 = mont64_mul(&m, w3, w3);
                uint64_t t34 = mont64_halve(&m, w6);
                if (e4 >= 0) {
                    uint64_t w10 = mont64_mul(&m, w5, w5);
                    t34 = mont64_add(&m, t34, mont64_halve_k(&m, w10, 4));
                }
                num = (s34 > 0) ? mont64_add(&m, num, t34) : mont64_sub(&m, num, t34);
            }
            if (idx == 0) num = mont64_add(&m, num, mont64_dbl(&m, num));
            acc = mont64_add(&m, acc, num);
        }
        uint64_t r = mont64_from(&m, mont64_mul(&m, acc, rd));
        accum64(out, r, N_mod);
    }
}

/* ==================== P-smooth tree walks (32-bit Barrett + 64-bit Mont) ==================== */

static uint64_t compute_tree_lcm(const Config *cfg, uint64_t root, int start_idx, uint64_t cap) {
    uint64_t limit = cfg->M_max / root;
    u128 L = 1;
    for (int i = start_idx; i < cfg->num_primes; i++) {
        uint64_t p = cfg->primes[i];
        uint64_t pk = 1;
        while (pk <= limit / p) pk *= p;
        L *= pk;
        if (L * (u128)root >= (u128)cap) return 0;
    }
    return (uint64_t)L;
}

static void walk_tree32(const Config *cfg, Mod32 m, uint64_t root, uint32_t L,
                        uint64_t s, uint32_t w_s, int start_idx, uint32_t *acc) {
    uint64_t M = root * s;
    uint32_t q = m.q;
    int64_t k = (int64_t)((M - 1) >> 1);
    int64_t d = cfg->d;
    int64_t e1 = d + 1 - 3 * k;

    if (e1 >= 0 && M > 1) {
        int64_t e2 = d - 1 - 5 * k;
        int64_t e3 = d - 1 - 6 * k;
        int64_t e4 = d - 4 - 10 * k;
        int s12 = ((k >> 1) & 1) ? -1 : 1;
        int s34 = (k & 1) ? -1 : 1;

        uint32_t w2 = mod32_mul(w_s, w_s, m);
        uint32_t w3 = mod32_mul(w2, w_s, m);
        uint32_t t12 = mod32_dbl(w3, q);
        uint32_t w5 = 0;
        if (e2 >= 0) {
            w5 = mod32_mul(w3, w2, m);
            t12 = mod32_add(t12, mod32_halve(w5, q), q);
        }
        uint32_t num = (s12 > 0) ? t12 : mod32_neg(t12, q);
        if (e3 >= 0) {
            uint32_t w6 = mod32_mul(w3, w3, m);
            uint32_t t34 = mod32_halve(w6, q);
            if (e4 >= 0) {
                uint32_t w10 = mod32_mul(w5, w5, m);
                t34 = mod32_add(t34, mod32_halve_k(w10, q, 4), q);
            }
            num = (s34 > 0) ? mod32_add(num, t34, q) : mod32_sub(num, t34, q);
        }
        uint32_t cof = (uint32_t)(L / s);
        if (cof > 1) num = mod32_mul(num, cof, m);
        *acc = mod32_add(*acc, num, q);
    }

    uint64_t max_p = cfg->M_max / M;
    for (int i = start_idx; i < cfg->num_primes; i++) {
        uint64_t p = cfg->primes[i];
        if (p > max_p) break;
        uint32_t w_child = mod32_pow_small(w_s, p, m);
        w_child = mod32_halve_k(w_child, q, cfg->prime_half[i]);
        walk_tree32(cfg, m, root, L, s * p, w_child, i, acc);
    }
}

static void walk_tree64(const Config *cfg, const Mont64 *m, uint64_t root, uint64_t L,
                        uint64_t s, uint64_t w_s, int start_idx, uint64_t *acc) {
    uint64_t M = root * s;
    int64_t k = (int64_t)((M - 1) >> 1);
    int64_t d = cfg->d;
    int64_t e1 = d + 1 - 3 * k;

    if (e1 >= 0 && M > 1) {
        int64_t e2 = d - 1 - 5 * k;
        int64_t e3 = d - 1 - 6 * k;
        int64_t e4 = d - 4 - 10 * k;
        int s12 = ((k >> 1) & 1) ? -1 : 1;
        int s34 = (k & 1) ? -1 : 1;

        uint64_t w2 = mont64_mul(m, w_s, w_s);
        uint64_t w3 = mont64_mul(m, w2, w_s);
        uint64_t t12 = mont64_dbl(m, w3);
        uint64_t w5 = 0;
        if (e2 >= 0) {
            w5 = mont64_mul(m, w3, w2);
            t12 = mont64_add(m, t12, mont64_halve(m, w5));
        }
        uint64_t num = (s12 > 0) ? t12 : (t12 ? m->n - t12 : 0);
        if (e3 >= 0) {
            uint64_t w6 = mont64_mul(m, w3, w3);
            uint64_t t34 = mont64_halve(m, w6);
            if (e4 >= 0) {
                uint64_t w10 = mont64_mul(m, w5, w5);
                t34 = mont64_add(m, t34, mont64_halve_k(m, w10, 4));
            }
            num = (s34 > 0) ? mont64_add(m, num, t34) : mont64_sub(m, num, t34);
        }
        uint64_t cof = L / s;
        if (cof > 1) num = mont64_mul(m, num, mont64_to(m, cof));
        *acc = mont64_add(m, *acc, num);
    }

    uint64_t max_p = cfg->M_max / M;
    for (int i = start_idx; i < cfg->num_primes; i++) {
        uint64_t p = cfg->primes[i];
        if (p > max_p) break;
        uint64_t w_child = mont64_pow_small(m, w_s, p);
        w_child = mont64_halve_k(m, w_child, cfg->prime_half[i]);
        walk_tree64(cfg, m, root, L, s * p, w_child, i, acc);
    }
}

static void process_root(const Config *cfg, Partial *out, uint64_t root, int start_idx) {
    if (root > cfg->M_max) return;
    if (start_idx >= cfg->num_primes || root > cfg->M_max / cfg->primes[start_idx]) {
        eval_single(cfg, out, root);
        return;
    }

    uint64_t cap = (cfg->mode == 2) ? MOD32_CAP : MOD64_CAP;
    uint64_t L = compute_tree_lcm(cfg, root, start_idx, cap);
    if (L == 0) {
        out->subroots++;
        uint64_t p = cfg->primes[start_idx];
        for (uint64_t pk = 1; pk <= cfg->M_max / root; pk *= p) {
            process_root(cfg, out, root * pk, start_idx + 1);
            if (pk > cfg->M_max / (root * p)) break;
        }
        return;
    }

    uint64_t N_mod = L * root;
    uint64_t k0 = (root - 1) >> 1;
    out->modexps += 2;

    if (N_mod < MOD32_CAP) {
        uint32_t q = (uint32_t)N_mod;
        out->cores32++;
        Mod32 m = mod32_init(q);
        uint32_t rd = mod32_pow2((uint64_t)cfg->d, m);
        uint32_t x0 = mod32_pow2(k0, m);
        uint32_t w0 = mod32_inv(x0, q);
        uint32_t acc = 0;
        walk_tree32(cfg, m, root, (uint32_t)L, 1, w0, start_idx, &acc);
        uint32_t r = mod32_mul(acc, rd, m);
        accum32(out, r, q);
    } else {
        out->cores64++;
        Mont64 m;
        mont64_init(&m, N_mod);
        uint64_t rd = mont64_pow2(&m, (uint64_t)cfg->d);
        uint64_t w0 = mont64_pow_inv2(&m, k0);
        uint64_t acc = 0;
        walk_tree64(cfg, &m, root, L, 1, w0, start_idx, &acc);
        uint64_t r = mont64_from(&m, mont64_mul(&m, acc, rd));
        accum64(out, r, N_mod);
    }
}

/* ==================== Exact 96-bit fixed-point tail ==================== */

static void add_tail_term(Partial *out, int64_t e, uint64_t denom, bool negative) {
    /* Term is +- 2^e / denom with e < 0. In 96-bit fixed point: 2^(96 + e) / denom */
    int64_t shift = PRECISION + e;
    u128 q = 0;
    bool rem = true;
    if (shift >= 0) {
        u128 num = (u128)1 << shift;
        q = num / denom;
        rem = (q * denom != num);
    }
    out->sum += negative ? -(q + rem) : q;
    out->rounded++;
}

static void compute_tail(int64_t d, Partial *out) {
    /* Term 1: E1 = d + 1 - 3k < 0 */
    int64_t k1 = (d + 1 >= 0) ? ((d + 1) / 3 + 1) : 0;
    for (int64_t k = k1; k < k1 + 36; k++) {
        add_tail_term(out, d + 1 - 3 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
    }
    /* Term 2: E2 = d - 1 - 5k < 0 */
    int64_t k2 = (d - 1 >= 0) ? ((d - 1) / 5 + 1) : 0;
    for (int64_t k = k2; k < k2 + 24; k++) {
        add_tail_term(out, d - 1 - 5 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
    }
    /* Term 3: E3 = d - 1 - 6k < 0 */
    int64_t k3 = (d - 1 >= 0) ? ((d - 1) / 6 + 1) : 0;
    for (int64_t k = k3; k < k3 + 20; k++) {
        add_tail_term(out, d - 1 - 6 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
    }
    /* Term 4: E4 = d - 4 - 10k < 0 */
    int64_t k4 = (d - 4 >= 0) ? ((d - 4) / 10 + 1) : 0;
    for (int64_t k = k4; k < k4 + 14; k++) {
        add_tail_term(out, d - 4 - 10 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
    }
}

/* ==================== Multithreaded work-stealing driver ==================== */

typedef struct {
    const Config *cfg;
    uint64_t num_blocks;
    uint64_t chunk_blocks;
    atomic_uint_fast64_t next_block;
} Job;

typedef struct {
    Job *job;
    Partial partial;
} Worker;

static inline bool passes_extra_primes(const Config *cfg, uint64_t M) {
    /* Wheel already filters primes dividing wheel_mod (3, 5, 7) */
    int start = (cfg->wheel_mod == 210) ? 3 : (cfg->wheel_mod == 30) ? 2 : (cfg->wheel_mod == 6) ? 1 : 0;
    for (int i = start; i < cfg->num_primes; i++) {
        if (M % cfg->primes[i] == 0) return false;
    }
    return true;
}

static void *worker_fn(void *arg) {
    Worker *w = (Worker *)arg;
    Job *job = w->job;
    const Config *cfg = job->cfg;
    Partial *out = &w->partial;

    for (;;) {
        uint64_t lo = atomic_fetch_add_explicit(&job->next_block, job->chunk_blocks, memory_order_relaxed);
        if (lo >= job->num_blocks) break;
        uint64_t hi = lo + job->chunk_blocks;
        if (hi > job->num_blocks) hi = job->num_blocks;

        if (cfg->mode == 0) {
            /* Exact Smith M/3M: blocks of size 18 (odd M mod 18) */
            for (uint64_t b = lo; b < hi; b++) {
                uint64_t base = b * 18;
                /* mod 18 residues: 1,5,7,11,13,17 -> pair3; 9 -> single; 3,15 -> skipped */
                static const uint64_t p3[6] = {1, 5, 7, 11, 13, 17};
                for (int i = 0; i < 6; i++) {
                    uint64_t M = base + p3[i];
                    if (M <= cfg->M_max) eval_smith_pair3(cfg, out, M);
                }
                uint64_t M9 = base + 9;
                if (M9 <= cfg->M_max) eval_single(cfg, out, M9);
            }
        } else {
            /* P-smooth tree using wheel_mod */
            uint64_t wmod = cfg->wheel_mod;
            int wlen = cfg->wheel_len;
            for (uint64_t b = lo; b < hi; b++) {
                uint64_t base = b * wmod;
                for (int i = 0; i < wlen; i++) {
                    uint64_t M = base + cfg->wheel_res[i];
                    if (M > cfg->M_max) break;
                    if (passes_extra_primes(cfg, M)) {
                        process_root(cfg, out, M, 0);
                    }
                }
            }
        }
    }
    return NULL;
}

static void init_config(Config *cfg, uint64_t n, int mode, int P) {
    memset(cfg, 0, sizeof(*cfg));
    cfg->d = (int64_t)n - 1;
    cfg->M_max = (cfg->d + 1 >= 0) ? (uint64_t)(2 * ((cfg->d + 1) / 3) + 1) : 0;
    cfg->mode = mode;
    cfg->P = P;

    if (mode >= 1 && P >= 3) {
        for (int i = 0; i < MAX_P_IDX && ODD_PRIMES[i] <= (uint64_t)P; i++) {
            cfg->primes[cfg->num_primes] = ODD_PRIMES[i];
            cfg->prime_half[cfg->num_primes] = (int)((ODD_PRIMES[i] - 1) >> 1);
            cfg->num_primes++;
        }
    }

    /* Build wheel */
    if (mode >= 1) {
        if (P >= 7) cfg->wheel_mod = 210;
        else if (P >= 5) cfg->wheel_mod = 30;
        else if (P >= 3) cfg->wheel_mod = 6;
        else cfg->wheel_mod = 2;

        for (uint64_t r = 1; r < cfg->wheel_mod; r += 2) {
            bool ok = true;
            if (cfg->wheel_mod >= 6 && r % 3 == 0) ok = false;
            if (cfg->wheel_mod >= 30 && r % 5 == 0) ok = false;
            if (cfg->wheel_mod >= 210 && r % 7 == 0) ok = false;
            if (ok) cfg->wheel_res[cfg->wheel_len++] = r;
        }
    }
}

static int parse_u64(const char *s, uint64_t lo, uint64_t hi, uint64_t *out) {
    if (!s || *s < '0' || *s > '9') return 0;
    char *end; errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno || *end || v < lo || v > hi) return 0;
    *out = v; return 1;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s <smith3m|smooth> <n> [P=19] [width=32] [threads=1]\n", argv[0]);
        return 2;
    }
    int mode = (strcmp(argv[1], "smith3m") == 0) ? 0 : (strcmp(argv[1], "smooth") == 0) ? 1 : (strcmp(argv[1], "smooth32") == 0) ? 2 : -1;
    if (mode < 0) {
        fprintf(stderr, "unknown mode %s\n", argv[1]);
        return 2;
    }
    uint64_t n, p64 = 19, w64 = 32, t64 = 1;
    if (!parse_u64(argv[2], 1, UINT64_MAX / 4, &n) || (argc > 3 && !parse_u64(argv[3], 1, 23, &p64)) ||
        (argc > 4 && !parse_u64(argv[4], 1, 64, &w64)) || (argc > 5 && !parse_u64(argv[5], 1, 16, &t64)) || argc > 6) {
        fprintf(stderr, "usage: %s <smith3m|smooth> <n>=1..> [P=19] [width=1..64] [threads=1..16]\n", argv[0]);
        return 2;
    }
    if (p64 != 1 && p64 != 3 && p64 != 5 && p64 != 7 && p64 != 11 && p64 != 13 && p64 != 17 && p64 != 19 && p64 != 23) {
        fprintf(stderr, "P must be one of 1,3,5,7,11,13,17,19,23\n");
        return 2;
    }
    int P = (int)p64;
    unsigned width = (unsigned)w64, threads = (unsigned)t64;

    Config cfg;
    init_config(&cfg, n, mode, P);

    double start = wall_time();

    uint64_t block_size = (mode == 0) ? 18 : cfg.wheel_mod;
    uint64_t num_blocks = (cfg.M_max / block_size) + 1;
    uint64_t chunk_blocks = (mode == 0) ? 256 : (cfg.wheel_mod == 210 ? 32 : 256);
    if (threads > 1) {
        uint64_t target = (num_blocks + 8 * threads - 1) / (8 * threads);
        if (target < 4) target = 4;
        if (chunk_blocks > target) chunk_blocks = target;
    }

    Job job = { .cfg = &cfg, .num_blocks = num_blocks, .chunk_blocks = chunk_blocks, .next_block = 0 };
    Worker workers[16];
    memset(workers, 0, sizeof(workers));
    pthread_t handles[16];

    for (unsigned i = 0; i < threads; i++) workers[i].job = &job;
    for (unsigned i = 0; i + 1 < threads; i++) {
        pthread_create(&handles[i], NULL, worker_fn, &workers[i]);
    }
    worker_fn(&workers[threads - 1]);
    for (unsigned i = 0; i + 1 < threads; i++) {
        pthread_join(handles[i], NULL);
    }

    Partial out = {0};
    for (unsigned i = 0; i < threads; i++) {
        out.sum += workers[i].partial.sum;
        out.rounded += workers[i].partial.rounded;
        out.modexps += workers[i].partial.modexps;
        out.cores32 += workers[i].partial.cores32;
        out.cores64 += workers[i].partial.cores64;
        out.subroots += workers[i].partial.subroots;
    }

    compute_tail(cfg.d, &out);

    u128 lo = (out.sum - 1) & FIXED_MASK;
    u128 hi = (out.sum + out.rounded + 1) & FIXED_MASK;
    uint64_t lower_window = (uint64_t)(lo >> (PRECISION - width));
    uint64_t upper_window = (uint64_t)(hi >> (PRECISION - width));
    bool certified = (lower_window == upper_window);

    double seconds = wall_time() - start;
    struct rusage usage = {0};
    getrusage(RUSAGE_SELF, &usage);
#ifdef __APPLE__
    uint64_t rss_bytes = (uint64_t)usage.ru_maxrss;
#else
    uint64_t rss_bytes = (uint64_t)usage.ru_maxrss * 1024;
#endif

    printf("{\"method\":\"%s\",\"P\":%d,\"n\":%" PRIu64 ",\"width\":%u,\"threads\":%u,"
           "\"certified\":%s,\"window\":",
           argv[1], mode == 0 ? 3 : P, n, width, threads, certified ? "true" : "false");
    if (certified) {
        putchar('"');
        for (unsigned i = width; i > 0; --i)
            putchar('0' + ((lower_window >> (i - 1)) & 1));
        putchar('"');
    } else {
        fputs("null", stdout);
    }
    printf(",\"seconds\":%.6f,\"rss_bytes\":%" PRIu64 ",\"modexps\":%" PRIu64
           ",\"cores32\":%" PRIu64 ",\"cores64\":%" PRIu64 ",\"subroots\":%" PRIu64
           ",\"rounded\":%" PRIu64 "}\n",
           seconds, rss_bytes, out.modexps, out.cores32, out.cores64, out.subroots, out.rounded);
    return certified ? 0 : 1;
}

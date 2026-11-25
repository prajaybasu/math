/*
 * euler_grouped.c — Segmented full prime-power partial-fraction decomposition
 * on the Euler/Hutton series for pi, using 32-bit Barrett reduction and a
 * 96-bit certified fixed-point kernel, O(sqrt(n) + B) memory, and pthreads.
 *
 * Computes the certified binary window of {2^(n-1) * pi} (matching bellard_bench).
 *
 * Key properties:
 *   - Only ONE denominator family M = 2k+1 up to M_max ~ (2/3)*n (33% smaller than Bellard)
 *   - Euler's criterion collapses 2^(-m*k_u) mod p so 2^d mod p factors out completely:
 *       C(p, d) == 2^d * A(p) (mod p)  ->  ONLY ONE mod-exp per odd prime p <= 2n/3!
 *   - For p > M2, only the first family at M = p contributes: A(p) = +-2 mod p.
 *   - Period folding for tiny q with 4*q*phi(q) < T eliminates small-q bottlenecks
 *   - Segmented odd-only sieve keeps RSS ~ a few MB even at n = 10^9!
 *
 * Compile:
 *   cc -O3 -pthread -o euler_grouped euler_grouped.c -lm
 *
 * Usage:
 *   ./euler_grouped <n> [width=32] [threads=1]
 */

#define _DARWIN_C_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <inttypes.h>
#include <math.h>
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

enum { PRECISION = 96, SEG_BITS = 1 << 16, PRE_PERIOD = 3 * 5 * 7 * 11 * 13 }; /* 65K odd numbers = 8 KB L1 bitset */
#define FIXED_MASK (((u128)1 << PRECISION) - 1)

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

static inline u128 fixed_fraction32(uint32_t r, uint32_t q) {
    uint64_t z = (uint64_t)r << 32;
    uint64_t a = z / q;
    z = (z - a * q) << 32;
    uint64_t b = z / q;
    z = (z - b * q) << 32;
    return ((u128)a << 64) | (b << 32) | (z / q);
}

static inline uint64_t gcd64(uint64_t a, uint64_t b) {
    while (b) { uint64_t t = a % b; a = b; b = t; }
    return a;
}

/* ==================== Euler/Hutton prime & prime-power evaluators ==================== */

typedef struct {
    int64_t d;
    uint64_t M1, M2, M3, M4; /* max odd M for each of the 4 terms */
    uint32_t *base_primes;
    uint32_t num_base_primes;
    uint32_t first_big;      /* index of first base prime > 61 */
    uint32_t last_bp;        /* largest base prime (always >= 61) */
    uint64_t *pattern;       /* pre-sieved 64-bit word pattern for {3,5,7,11,13} */
    uint32_t wp[12];         /* word-masked primes {17..61} */
    uint64_t wmask[12][61];  /* wmask[j][r] for word starting at lo % wp[j] == r */
    uint32_t *pp_q;          /* prime powers q = p^e (e >= 2) <= M1 */
    uint32_t *pp_p;          /* underlying prime p */
    uint32_t num_pp;
} Config;

typedef struct {
    u128 sum;
    uint64_t rounded;
    uint64_t modexps;
    uint64_t primes;
    uint64_t prime_powers;
} Partial;

static inline void accum32(Partial *out, uint32_t r, uint32_t q) {
    out->sum += fixed_fraction32(r, q);
    out->rounded++;
}

/*
 * Exact periodic sum for a single term j (with step multiplier r_step = 2^(-m_j * q) mod q
 * or 2^(-m_j) mod p for primes) over odd u = 2t+1 <= U with p \nmid u:
 *   sum_{0 <= t <= T, p \nmid (2t+1)} (2t+1)^(-1) * sign(t) * cur_pow (mod q)
 * where sign(t) has period 4 (for s12) or 2 (for s34).
 */
static uint32_t sum_term_periodic(uint32_t q, uint32_t p, Mod32 m, uint64_t U,
                                  uint32_t init_pow, uint32_t step_pow,
                                  bool is_s12) {
    if (U == 0) return 0;
    uint64_t T = (U - 1) >> 1; /* t in [0, T] */
    uint64_t count = T + 1;

    /* Find multiplicative order of step_pow mod q (divides phi(q)) */
    uint64_t phi = (uint64_t)(q / p) * (p - 1);
    uint64_t ord = 1;
    uint32_t cur = step_pow;
    /* Only compute exact order if 4 * q * phi < count */
    uint64_t max_per = 4ULL * q * phi;
    if (max_per < count) {
        /* Exact period divides 4 * q * ord */
        while (cur != 1 && ord <= phi) {
            cur = mod32_mul(cur, step_pow, m);
            ord++;
        }
        uint64_t per = q;
        uint64_t g = gcd64(per, ord);
        per = (per / g) * ord;
        uint64_t s_per = is_s12 ? 4 : 2;
        g = gcd64(per, s_per);
        per = (per / g) * s_per;

        uint64_t full = count / per;
        uint64_t rem = count % per;

        uint32_t per_sum = 0, rem_sum = 0;
        uint32_t pw = init_pow;
        uint32_t u_mod_q = 1;
        uint32_t u_mod_p = 1;
        uint64_t k_mod4 = ((q - 1) >> 1) & 3;
        uint64_t q_mod4 = q & 3;

        for (uint64_t t = 0; t < per; t++) {
            if (u_mod_p != 0) {
                uint32_t inv_u = mod32_inv(u_mod_q, q);
                uint32_t term = mod32_mul(inv_u, pw, m);
                bool neg = is_s12 ? ((k_mod4 >> 1) & 1) : (k_mod4 & 1);
                if (neg) term = mod32_neg(term, q);
                per_sum = mod32_add(per_sum, term, q);
                if (t < rem) rem_sum = mod32_add(rem_sum, term, q);
            }
            pw = mod32_mul(pw, step_pow, m);
            u_mod_q += 2; if (u_mod_q >= q) u_mod_q -= q;
            u_mod_p += 2; if (u_mod_p >= p) u_mod_p -= p;
            k_mod4 = (k_mod4 + q_mod4) & 3;
        }
        uint32_t total = mod32_mul((uint32_t)(full % q), per_sum, m);
        return mod32_add(total, rem_sum, q);
    }

    /* Direct sum with Montgomery batch inversion in chunks of 256 */
    uint32_t acc = 0;
    uint32_t pw = init_pow;
    uint32_t u_mod_q = 1;
    uint32_t u_mod_p = 1;
    uint64_t k_mod4 = ((q - 1) >> 1) & 3;
    uint64_t q_mod4 = q & 3;

    uint32_t buf_u[256], buf_pref[256], buf_val[256];
    uint64_t t = 0;
    while (t < count) {
        int nb = 0;
        uint32_t prod = 1;
        while (t < count && nb < 256) {
            if (u_mod_p != 0) {
                buf_u[nb] = u_mod_q;
                buf_pref[nb] = prod;
                prod = mod32_mul(prod, u_mod_q, m);
                bool neg = is_s12 ? ((k_mod4 >> 1) & 1) : (k_mod4 & 1);
                buf_val[nb] = neg ? mod32_neg(pw, q) : pw;
                nb++;
            }
            pw = mod32_mul(pw, step_pow, m);
            u_mod_q += 2; if (u_mod_q >= q) u_mod_q -= q;
            u_mod_p += 2; if (u_mod_p >= p) u_mod_p -= p;
            k_mod4 = (k_mod4 + q_mod4) & 3;
            t++;
        }
        if (nb > 0) {
            uint32_t inv_prod = mod32_inv(prod, q);
            for (int i = nb - 1; i >= 0; i--) {
                uint32_t inv_u = mod32_mul(inv_prod, buf_pref[i], m);
                inv_prod = mod32_mul(inv_prod, buf_u[i], m);
                acc = mod32_add(acc, mod32_mul(inv_u, buf_val[i], m), q);
            }
        }
    }
    return acc;
}

/* Evaluate an odd prime p <= M1 */
static inline void eval_prime(const Config *cfg, Partial *out, uint32_t p,
                              uint32_t *inv_buf, uint32_t *pref_buf) {
    out->primes++;
    Mod32 m = mod32_init(p);

    /* Fast path: p > M2 => ONLY u = 1 in Term 1 (since M2 > M3 > M1/3 > M4)! */
    if ((uint64_t)p > cfg->M2) {
        /* chi_2(p) * s12((p-1)/2) == (-1)^((p-1)/2) == +1 if p%4==1 else -1 */
        out->modexps++;
        uint32_t r = mod32_pow2((uint64_t)(cfg->d + 1), m);
        if ((p & 3) == 3) r = mod32_neg(r, p);
        accum32(out, r, p);
        return;
    }

    /* Medium/small prime: C(p, d) == 2^d * A(p) mod p */
    uint64_t U1 = cfg->M1 / p;
    uint64_t U2 = cfg->M2 / p;
    uint64_t U3 = cfg->M3 / p;
    uint64_t U4 = cfg->M4 / p;

    /* Legendre symbol (2/p): +1 if p == 1,7 mod 8; -1 if p == 3,5 mod 8 */
    bool chi2_neg = ((p & 7) == 3 || (p & 7) == 5);

    uint32_t inv8    = mod32_halve_k(1, p, 3);
    uint32_t inv32   = mod32_halve_k(1, p, 5);
    uint32_t inv64   = mod32_halve_k(1, p, 6);
    uint32_t inv1024 = mod32_halve_k(1, p, 10);

    uint32_t A = 0;
    uint64_t T1 = (U1 - 1) >> 1;

    /* If small prime where periodic folding helps, use sum_term_periodic */
    if (4ULL * p * (p - 1) < (T1 + 1)) {
        uint32_t s1 = sum_term_periodic(p, p, m, U1, 2 % p, inv8, true);
        uint32_t s2 = sum_term_periodic(p, p, m, U2, mod32_halve(1, p), inv32, true);
        uint32_t t12 = mod32_add(s1, s2, p);
        if (chi2_neg) t12 = mod32_neg(t12, p);
        uint32_t s3 = sum_term_periodic(p, p, m, U3, mod32_halve(1, p), inv64, false);
        uint32_t s4 = sum_term_periodic(p, p, m, U4, mod32_halve_k(1, p, 4), inv1024, false);
        A = mod32_add(t12, mod32_add(s3, s4, p), p);
    } else {
        /*
         * Joint batch-inversion pass over odd u = 2t+1 <= U1 (p \nmid u),
         * accumulating all active terms (1..4) in ONE inversion pass!
         */
        uint64_t count = T1 + 1;
        uint32_t pw1 = 2 % p;
        uint32_t pw2 = mod32_halve(1, p);
        uint32_t pw3 = pw2;
        uint32_t pw4 = mod32_halve_k(1, p, 4);

        uint32_t u_mod_p = 1;
        uint64_t k_mod4 = ((p - 1) >> 1) & 3;
        uint64_t p_mod4 = p & 3;

        uint64_t t = 0;
        while (t < count) {
            int nb = 0;
            uint32_t prod = 1;
            while (t < count && nb < 256) {
                uint64_t u = (t << 1) + 1;
                if (u_mod_p != 0) {
                    inv_buf[nb] = u_mod_p;
                    pref_buf[nb] = prod;
                    prod = mod32_mul(prod, u_mod_p, m);

                    uint32_t t12 = pw1;
                    if (u <= U2) t12 = mod32_add(t12, pw2, p);
                    bool neg12 = (((k_mod4 >> 1) & 1) != 0) ^ chi2_neg;
                    uint32_t val = neg12 ? mod32_neg(t12, p) : t12;

                    if (u <= U3) {
                        uint32_t t34 = pw3;
                        if (u <= U4) t34 = mod32_add(t34, pw4, p);
                        bool neg34 = (k_mod4 & 1) != 0;
                        val = neg34 ? mod32_sub(val, t34, p) : mod32_add(val, t34, p);
                    }
                    /* Temporarily store val in inv_buf[nb + 256] */
                    inv_buf[nb + 256] = val;
                    nb++;
                }
                pw1 = mod32_mul(pw1, inv8, m);
                if (u < U2) pw2 = mod32_mul(pw2, inv32, m);
                if (u < U3) pw3 = mod32_mul(pw3, inv64, m);
                if (u < U4) pw4 = mod32_mul(pw4, inv1024, m);
                u_mod_p += 2; if (u_mod_p >= p) u_mod_p -= p;
                k_mod4 = (k_mod4 + p_mod4) & 3;
                t++;
            }
            if (nb > 0) {
                uint32_t inv_prod = mod32_inv(prod, p);
                for (int i = nb - 1; i >= 0; i--) {
                    uint32_t inv_u = mod32_mul(inv_prod, pref_buf[i], m);
                    inv_prod = mod32_mul(inv_prod, inv_buf[i], m);
                    A = mod32_add(A, mod32_mul(inv_u, inv_buf[i + 256], m), p);
                }
            }
        }
    }

    out->modexps++;
    uint32_t rd = mod32_pow2((uint64_t)cfg->d, m);
    uint32_t r = mod32_mul(A, rd, m);
    accum32(out, r, p);
}

/* Evaluate an odd prime power q = p^e (e >= 2) <= M1 */
static void eval_prime_power(const Config *cfg, Partial *out, uint32_t q, uint32_t p) {
    out->prime_powers++;
    Mod32 m = mod32_init(q);

    uint64_t U1 = cfg->M1 / q;
    uint64_t U2 = cfg->M2 / q;
    uint64_t U3 = cfg->M3 / q;
    uint64_t U4 = cfg->M4 / q;

    /* For q = p^e, k_u = q*t + (q-1)/2.
       Need 2^(-m_j * (q-1)/2) and step 2^(-m_j * q) mod q. */
    out->modexps += 2;
    uint32_t p2_half = mod32_pow2((q - 1) >> 1, m);
    uint32_t w_half = mod32_inv(p2_half, q);       /* 2^(-(q-1)/2) mod q */
    uint32_t w_q = mod32_halve(mod32_mul(w_half, w_half, m), q); /* 2^(-q) mod q */

    uint32_t wh2 = mod32_mul(w_half, w_half, m);
    uint32_t wh3 = mod32_mul(wh2, w_half, m);
    uint32_t wh5 = mod32_mul(wh3, wh2, m);
    uint32_t wh6 = mod32_mul(wh3, wh3, m);
    uint32_t wh10 = mod32_mul(wh5, wh5, m);

    uint32_t wq2 = mod32_mul(w_q, w_q, m);
    uint32_t wq3 = mod32_mul(wq2, w_q, m);
    uint32_t wq5 = mod32_mul(wq3, wq2, m);
    uint32_t wq6 = mod32_mul(wq3, wq3, m);
    uint32_t wq10 = mod32_mul(wq5, wq5, m);

    uint32_t s1 = sum_term_periodic(q, p, m, U1, mod32_dbl(wh3, q), wq3, true);
    uint32_t s2 = sum_term_periodic(q, p, m, U2, mod32_halve(wh5, q), wq5, true);
    uint32_t s3 = sum_term_periodic(q, p, m, U3, mod32_halve(wh6, q), wq6, false);
    uint32_t s4 = sum_term_periodic(q, p, m, U4, mod32_halve_k(wh10, q, 4), wq10, false);

    uint32_t A = mod32_add(mod32_add(s1, s2, q), mod32_add(s3, s4, q), q);
    uint32_t rd = mod32_pow2((uint64_t)cfg->d, m);
    uint32_t r = mod32_mul(A, rd, m);
    accum32(out, r, q);
}

/* ==================== Exact 96-bit tail ==================== */

static void add_tail_term(Partial *out, int64_t e, uint64_t denom, bool negative) {
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
    int64_t k1 = (d + 1 >= 0) ? ((d + 1) / 3 + 1) : 0;
    for (int64_t k = k1; k < k1 + 36; k++)
        add_tail_term(out, d + 1 - 3 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
    int64_t k2 = (d - 1 >= 0) ? ((d - 1) / 5 + 1) : 0;
    for (int64_t k = k2; k < k2 + 24; k++)
        add_tail_term(out, d - 1 - 5 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
    int64_t k3 = (d - 1 >= 0) ? ((d - 1) / 6 + 1) : 0;
    for (int64_t k = k3; k < k3 + 20; k++)
        add_tail_term(out, d - 1 - 6 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
    int64_t k4 = (d - 4 >= 0) ? ((d - 4) / 10 + 1) : 0;
    for (int64_t k = k4; k < k4 + 14; k++)
        add_tail_term(out, d - 4 - 10 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
}

/* ==================== Segmented parallel sieve + evaluation ==================== */

typedef struct {
    const Config *cfg;
    uint64_t seg_start_idx;
    uint64_t num_segs;
    atomic_uint_fast64_t next_small_p;
    atomic_uint_fast64_t next_seg;
    atomic_uint_fast64_t next_pp;
} Job;

typedef struct {
    Job *job;
    Partial partial;
} Worker;

static void *worker_fn(void *arg) {
    Worker *w = (Worker *)arg;
    Job *job = w->job;
    const Config *cfg = job->cfg;
    Partial *out = &w->partial;

    /* Per-thread segmented sieve bitset: SEG_BITS odd integers = SEG_BITS/64 uint64s (8 KB L1) */
    uint64_t *bits = (uint64_t *)malloc((SEG_BITS / 64) * sizeof(uint64_t));
    uint32_t inv_buf[512];
    uint32_t pref_buf[256];

    /* 0. Parallel work-stealing over small primes (base_primes, chunk = 1 for load balance) */
    for (;;) {
        uint64_t i = atomic_fetch_add_explicit(&job->next_small_p, 1, memory_order_relaxed);
        if (i >= cfg->num_base_primes) break;
        uint32_t p = cfg->base_primes[i];
        if (p <= cfg->M1) eval_prime(cfg, out, p, inv_buf, pref_buf);
    }

    /* 1. Process prime segments starting strictly above base_primes (lo_idx is 64-aligned) */
    uint64_t max_idx = (cfg->M1 > 0) ? ((cfg->M1 - 1) >> 1) : 0;
    for (;;) {
        uint64_t seg = atomic_fetch_add_explicit(&job->next_seg, 1, memory_order_relaxed);
        if (seg >= job->num_segs) break;

        uint64_t lo_idx = job->seg_start_idx + seg * SEG_BITS;
        uint64_t hi_idx = lo_idx + SEG_BITS;
        if (lo_idx > max_idx) break;
        if (hi_idx > max_idx + 1) hi_idx = max_idx + 1;
        uint64_t len = hi_idx - lo_idx;
        uint64_t nw = (len + 63) >> 6;

        /* Copy pre-sieved pattern for {3, 5, 7, 11, 13} */
        uint64_t wofs = (lo_idx >> 6) % PRE_PERIOD;
        for (uint64_t wi = 0; wi < nw; wi++) {
            bits[wi] = cfg->pattern[wofs];
            if (++wofs == PRE_PERIOD) wofs = 0;
        }

        /* Apply precomputed 64-bit word masks for {17..61} */
        for (int j = 0; j < 12; j++) {
            uint32_t p = cfg->wp[j];
            uint32_t r = (uint32_t)(lo_idx % p);
            uint32_t st = 64 % p;
            const uint64_t *mk = cfg->wmask[j];
            for (uint64_t wi = 0; wi < nw; wi++) {
                bits[wi] |= mk[r];
                r += st;
                if (r >= p) r -= p;
            }
        }

        /* Mark remaining base primes p >= 67 */
        uint64_t lo_val = (lo_idx << 1) + 1;
        uint64_t hi_val = ((hi_idx - 1) << 1) + 1;

        for (uint32_t i = cfg->first_big; i < cfg->num_base_primes; i++) {
            uint64_t p = cfg->base_primes[i];
            uint64_t p2 = p * p;
            if (p2 > hi_val) break;
            uint64_t start = (p2 >= lo_val) ? p2 : ((lo_val + p - 1) / p) * p;
            if ((start & 1) == 0) start += p;
            uint64_t idx = (start - lo_val) >> 1;
            for (; idx < len; idx += p) {
                bits[idx >> 6] |= 1ULL << (idx & 63);
            }
        }
        if (len & 63) bits[nw - 1] |= ~0ULL << (len & 63);

        for (uint64_t wi = 0; wi < nw; wi++) {
            uint64_t x = ~bits[wi];
            while (x) {
                int b = __builtin_ctzll(x);
                x &= x - 1;
                uint32_t p = (uint32_t)(((lo_idx + (wi << 6) + (uint64_t)b) << 1) + 1);
                if (p <= cfg->last_bp) continue;
                eval_prime(cfg, out, p, inv_buf, pref_buf);
            }
        }
    }

    /* 2. Process prime powers q = p^e (e >= 2) with chunk = 1 for load balance */
    for (;;) {
        uint64_t i = atomic_fetch_add_explicit(&job->next_pp, 1, memory_order_relaxed);
        if (i >= cfg->num_pp) break;
        eval_prime_power(cfg, out, cfg->pp_q[i], cfg->pp_p[i]);
    }

    free(bits);
    return NULL;
}

static void build_base_primes_and_pp(Config *cfg) {
    uint64_t limit = (uint64_t)sqrt((double)cfg->M1) + 2;
    if (limit < 61) limit = 61;
    uint8_t *is_comp = (uint8_t *)calloc(limit + 1, 1);
    uint32_t cap = (uint32_t)(limit / 2 + 16);
    cfg->base_primes = (uint32_t *)malloc(cap * sizeof(uint32_t));
    cfg->num_base_primes = 0;

    uint32_t pp_cap = cap * 2;
    cfg->pp_q = (uint32_t *)malloc(pp_cap * sizeof(uint32_t));
    cfg->pp_p = (uint32_t *)malloc(pp_cap * sizeof(uint32_t));
    cfg->num_pp = 0;

    for (uint64_t p = 3; p <= limit; p += 2) {
        if (!is_comp[p]) {
            cfg->base_primes[cfg->num_base_primes++] = (uint32_t)p;
            for (uint64_t j = p * p; j <= limit; j += 2 * p) is_comp[j] = 1;
            /* Record all powers p^e <= M1 with e >= 2 */
            uint64_t q = p * p;
            while (q <= cfg->M1) {
                if (cfg->num_pp >= pp_cap) {
                    pp_cap *= 2;
                    cfg->pp_q = (uint32_t *)realloc(cfg->pp_q, pp_cap * sizeof(uint32_t));
                    cfg->pp_p = (uint32_t *)realloc(cfg->pp_p, pp_cap * sizeof(uint32_t));
                }
                cfg->pp_q[cfg->num_pp] = (uint32_t)q;
                cfg->pp_p[cfg->num_pp] = (uint32_t)p;
                cfg->num_pp++;
                if (q > cfg->M1 / p) break;
                q *= p;
            }
        }
    }
    free(is_comp);

    cfg->last_bp = cfg->base_primes[cfg->num_base_primes - 1];
    cfg->first_big = 0;
    while (cfg->first_big < cfg->num_base_primes && cfg->base_primes[cfg->first_big] <= 61)
        cfg->first_big++;

    /* Precompute 64-bit word masks for {17..61} */
    static const uint32_t wps[12] = {17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
    for (int j = 0; j < 12; j++) {
        uint32_t p = wps[j], h = (p - 1) / 2;
        cfg->wp[j] = p;
        for (uint32_t r = 0; r < p; r++) {
            uint64_t mk = 0;
            for (int b = 0; b < 64; b++) {
                if ((r + (uint32_t)b) % p == h) mk |= 1ULL << b;
            }
            cfg->wmask[j][r] = mk;
        }
    }

    /* Precompute pre-sieved pattern for {3, 5, 7, 11, 13} */
    cfg->pattern = (uint64_t *)calloc(PRE_PERIOD, sizeof(uint64_t));
    static const unsigned pr[5] = {3, 5, 7, 11, 13};
    for (uint64_t i = 0; i < (uint64_t)PRE_PERIOD * 64; i++) {
        uint64_t v = (i << 1) + 1;
        for (int k = 0; k < 5; k++) {
            if (v % pr[k] == 0) {
                cfg->pattern[i >> 6] |= 1ULL << (i & 63);
                break;
            }
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
    if (argc < 2) {
        fprintf(stderr, "usage: %s <n> [width=32] [threads=1]\n", argv[0]);
        return 2;
    }
    uint64_t n, w64 = 32, t64 = 1;
    if (!parse_u64(argv[1], 1, UINT64_MAX / 4, &n) || (argc > 2 && !parse_u64(argv[2], 1, 64, &w64)) ||
        (argc > 3 && !parse_u64(argv[3], 1, 16, &t64)) || argc > 4) {
        fprintf(stderr, "usage: %s <n>=1..> [width=1..64] [threads=1..16]\n", argv[0]);
        return 2;
    }
    unsigned width = (unsigned)w64, threads = (unsigned)t64;

    Config cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.d = (int64_t)n - 1;
    cfg.M1 = (cfg.d + 1 >= 0) ? (uint64_t)(2 * ((cfg.d + 1) / 3) + 1) : 0;
    cfg.M2 = (cfg.d - 1 >= 0) ? (uint64_t)(2 * ((cfg.d - 1) / 5) + 1) : 0;
    cfg.M3 = (cfg.d - 1 >= 0) ? (uint64_t)(2 * ((cfg.d - 1) / 6) + 1) : 0;
    cfg.M4 = (cfg.d - 4 >= 0) ? (uint64_t)(2 * ((cfg.d - 4) / 10) + 1) : 0;

    if (cfg.M1 >= (1ULL << 31)) {
        fprintf(stderr, "n too large for 32-bit Barrett (M1=%llu >= 2^31)\n", (unsigned long long)cfg.M1);
        return 2;
    }

    double start = wall_time();
    build_base_primes_and_pp(&cfg);

    uint64_t max_idx = (cfg.M1 > 0) ? ((cfg.M1 - 1) >> 1) : 0;
    uint64_t seg_start_idx = (((uint64_t)cfg.last_bp + 1) >> 1) & ~63ULL;
    uint64_t num_segs = (cfg.M1 > cfg.last_bp && seg_start_idx <= max_idx)
                      ? (((max_idx - seg_start_idx) / SEG_BITS) + 1) : 0;

    Job job = { .cfg = &cfg, .seg_start_idx = seg_start_idx, .num_segs = num_segs,
                .next_small_p = 0, .next_seg = 0, .next_pp = 0 };
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
        out.primes += workers[i].partial.primes;
        out.prime_powers += workers[i].partial.prime_powers;
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

    printf("{\"method\":\"euler_grouped\",\"n\":%" PRIu64 ",\"width\":%u,\"threads\":%u,"
           "\"certified\":%s,\"window\":",
           n, width, threads, certified ? "true" : "false");
    if (certified) {
        putchar('"');
        for (unsigned i = width; i > 0; --i)
            putchar('0' + ((lower_window >> (i - 1)) & 1));
        putchar('"');
    } else {
        fputs("null", stdout);
    }
    printf(",\"seconds\":%.6f,\"rss_bytes\":%" PRIu64 ",\"modexps\":%" PRIu64
           ",\"primes\":%" PRIu64 ",\"prime_powers\":%" PRIu64 ",\"rounded\":%" PRIu64 "}\n",
           seconds, rss_bytes, out.modexps, out.primes, out.prime_powers, out.rounded);

    free(cfg.pattern);
    free(cfg.base_primes);
    free(cfg.pp_q);
    free(cfg.pp_p);
    return certified ? 0 : 1;
}

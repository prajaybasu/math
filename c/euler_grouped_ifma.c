/*
 * euler_grouped_ifma.c — AVX-512 IFMA vectorization of euler_grouped.c
 * (segmented full prime-power grouping on the Euler/Hutton series for pi).
 *
 * Computes the certified binary window of {2^(n-1) * pi} (same output as euler_grouped).
 *
 * Structure (A16 = 16*A(p), so every coefficient is an integer combination of 2^(d-4)):
 *   r(p) = A16(p) * 2^(d-4) mod p,  pi-window += r(p)/p  (certified fixed point)
 *
 *   FAST   primes  p > M1/3  : A16(p) = c(p), a small signed integer (|c| <= 49), so
 *                             r = c * 2^(d-4): ONE common-exponent modexp, 8 lanes/vector,
 *                             4 vectors interleaved, 52-bit IFMA Montgomery (lazy, [0,2p)).
 *   MEDIUM primes  B0 < p <= M1/3 : A16(p) = sum_u val(u)/u is accumulated as a fraction N/D
 *                             in each lane (no inversions inside the loop), all geometric
 *                             factors 2^(-m) updated by exact "small Montgomery" shifts;
 *                             then ONE joint exponentiation  2^(d-56) * D^(p-2)  (Fermat
 *                             inverse folded into the 2^d modexp: shared squarings).
 *   SMALL  primes  p <= B0 and all prime powers q=p^e: scalar, using exact
 *                             residue-class block sums (O(q) per q) or a direct batched pass.
 *
 *   The per-term contributions are converted to 100-bit fractions floor(r*2^100/p) in
 *   vector (5 x 20-bit digits via exact double arithmetic), summed exactly, and the total
 *   is truncated to the same 96-bit certified fixed point as euler_grouped.
 *
 * Compile:  gcc -O3 -march=native -pthread -o euler_grouped_ifma euler_grouped_ifma.c -lm
 * Usage:    ./euler_grouped_ifma <n> [width=32] [threads=1]
 * Env:      B0FRAC (default 0.09), SEGEPS (default 0.01)
 */
#define _GNU_SOURCE
#include <immintrin.h>
#include <x86intrin.h>
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
enum { PRECISION = 96 };
#define FIXED_MASK (((u128)1 << PRECISION) - 1)
#define SEGMAX (1u << 18)          /* odd numbers per sieve segment (32 KB bitset) */
#define PRE_PERIOD 15015u          /* 3*5*7*11*13 */
#define MASK52 ((1ULL << 52) - 1)
#define NVF 4                      /* fast vectors interleaved */
#define NVM 2                      /* medium vectors interleaved */

static double wall_time(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

/* ============================ scalar mod q (q < 2^32) ============================ */
typedef struct { uint64_t rec; uint64_t q; } Mod;
static inline Mod mod_init(uint64_t q) { return (Mod){UINT64_MAX / q, q}; }
static inline uint64_t mod_red(uint64_t z, Mod m) {
    uint64_t quo = (uint64_t)(((u128)z * m.rec) >> 64);
    uint64_t r = z - quo * m.q;
    while (r >= m.q) r -= m.q;
    return r;
}
static inline uint64_t smul(uint64_t a, uint64_t b, Mod m) { return mod_red(a * b, m); }
static inline uint64_t sadd(uint64_t a, uint64_t b, uint64_t q) { uint64_t s = a + b; return s >= q ? s - q : s; }
static inline uint64_t ssub(uint64_t a, uint64_t b, uint64_t q) { return a >= b ? a - b : a + q - b; }
static inline uint64_t sneg(uint64_t a, uint64_t q) { return a ? q - a : 0; }
static uint64_t spow2(uint64_t e, Mod m) {
    uint64_t r = 1 % m.q;
    for (int i = 63 - (e ? __builtin_clzll(e) : 63); i >= 0; i--) {
        r = smul(r, r, m);
        if ((e >> i) & 1) r = sadd(r, r, m.q);
    }
    return r;
}
static uint64_t spow(uint64_t b, uint64_t e, Mod m) {
    uint64_t r = 1 % m.q;
    while (e) { if (e & 1) r = smul(r, b, m); b = smul(b, b, m); e >>= 1; }
    return r;
}
static uint64_t sinv(uint64_t a, uint64_t q) {
    int64_t t = 0, nt = 1, r = (int64_t)q, nr = (int64_t)(a % q);
    while (nr) { int64_t qu = r / nr, tmp = t - qu * nt; t = nt; nt = tmp; tmp = r - qu * nr; r = nr; nr = tmp; }
    if (t < 0) t += (int64_t)q;
    return (uint64_t)t;
}
static inline u128 fixed_fraction(uint64_t r, uint64_t q) {
    uint64_t z = r << 32, a = z / q; z = (z - a * q) << 32;
    uint64_t b = z / q; z = (z - b * q) << 32;
    return ((u128)a << 64) | ((u128)b << 32) | (z / q);
}

/* ============================ config / stats ============================ */
typedef struct {
    int64_t d;
    uint64_t M1, M2, M3, M4, B, B0;
    uint32_t *bp; uint32_t nbp;            /* odd primes <= B */
    double *bp_inv;
    uint32_t *pp_q, *pp_p; uint32_t npp;   /* prime powers */
    uint32_t nsmall;                       /* bp[0..nsmall) <= B0 (scalar) */
    uint64_t *seg_lo; uint64_t nseg;       /* segment boundaries in odd-index space */
    uint64_t max_idx;
    uint64_t *pattern;                     /* presieve words (PRE_PERIOD words) */
    uint64_t wmask[12][64]; uint32_t wp[12]; uint32_t first_big;  /* word masks for 17..61 */
    uint64_t Ef, Em; int Lf, Lm; uint64_t t0f, t0m;
} Config;

enum { T_SIEVE, T_FAST, T_MEDLOOP, T_MEDEXP, T_SCALAR, T_N };
typedef struct {
    u128 sum;                /* scalar 96-bit terms */
    uint64_t vacc[5];        /* vector 20-bit digit sums */
    uint64_t rounded;
    uint64_t fast, medium, scal, pps;
    uint64_t modexp_sq;      /* lane-squarings in vector exponentiations */
    uint64_t lane_iters, lane_iters_useful;
    uint64_t scalar_iters, scalar_inv, scalar_modexp;
    uint64_t tsc[T_N];
    char pad[64];
} Partial;

/* ============================ vector IFMA primitives ============================ */
typedef __m512i V;
#define VZ _mm512_setzero_si512()
static inline V vset(uint64_t x) { return _mm512_set1_epi64((long long)x); }

/* Montgomery product a*b*2^-52 mod p, inputs < 2^52 with a*b < 2^52*p; output < 2p */
static inline V mm(V a, V b, V p, V pinv) {
    V lo = _mm512_madd52lo_epu64(VZ, a, b);
    V hi = _mm512_madd52hi_epu64(VZ, a, b);
    V m = _mm512_madd52lo_epu64(VZ, lo, pinv);
    __mmask8 c = _mm512_test_epi64_mask(lo, lo);
    V r = _mm512_madd52hi_epu64(hi, m, p);
    return _mm512_mask_add_epi64(r, c, r, vset(1));
}
/* (a*b + c*e) * 2^-52 mod p, one reduction; requires a*b + c*e < 2^52 * p */
static inline V mm2(V a, V b, V c, V e, V p, V pinv) {
    V lo = _mm512_madd52lo_epu64(_mm512_madd52lo_epu64(VZ, a, b), c, e);   /* < 2^53 */
    V hi = _mm512_madd52hi_epu64(_mm512_madd52hi_epu64(VZ, a, b), c, e);
    V m = _mm512_madd52lo_epu64(VZ, lo, pinv);                              /* uses lo mod 2^52 */
    V l52 = _mm512_and_si512(lo, vset(MASK52));
    hi = _mm512_add_epi64(hi, _mm512_srli_epi64(lo, 52));
    V r = _mm512_madd52hi_epu64(hi, m, p);
    return _mm512_mask_add_epi64(r, _mm512_test_epi64_mask(l52, l52), r, vset(1));
}
static inline V vdbl(V x, V p2) { V y = _mm512_add_epi64(x, x); return _mm512_min_epu64(y, _mm512_sub_epi64(y, p2)); }
static inline V vred(V x, V p) { return _mm512_min_epu64(x, _mm512_sub_epi64(x, p)); }
/* exact x * 2^-m mod p for x < p (result < p): x + ((x*(-1/p)) mod 2^m)*p, >> m */
#define VSHR(x, m, mask) _mm512_srli_epi64(_mm512_madd52lo_epu64((x), _mm512_and_si512(_mm512_madd52lo_epu64(VZ, (x), pinv), (mask)), p), (m))

static inline V vpinv(V p) {
    V x = _mm512_xor_si512(_mm512_mullo_epi64(p, vset(3)), vset(2));
    for (int i = 0; i < 4; i++) x = _mm512_mullo_epi64(x, _mm512_sub_epi64(vset(2), _mm512_mullo_epi64(p, x)));
    return _mm512_and_si512(_mm512_sub_epi64(VZ, x), vset(MASK52));
}
/* 2^t mod p for t in {52,53}, using double reciprocal */
static inline V vpow2small(uint64_t t, V p, __m512d invp) {
    V x = vset(1ULL << t);
    __m512d q = _mm512_roundscale_pd(_mm512_mul_pd(_mm512_cvtepu64_pd(x), invp), _MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC);
    V r = _mm512_sub_epi64(x, _mm512_mullo_epi64(_mm512_cvttpd_epu64(q), p));
    r = _mm512_mask_add_epi64(r, _mm512_cmplt_epi64_mask(r, VZ), r, p);
    return vred(r, p);
}
/* acc += floor(r * 2^100 / p) as 5 base-2^20 digits; r in [0,p) */
static inline void vfrac(Partial *o, V r, V p, __m512d invp, __mmask8 lanes, V acc[5]) {
    (void)o;
    for (int k = 0; k < 5; k++) {
        V z = _mm512_slli_epi64(r, 20);
        __m512d qd = _mm512_roundscale_pd(_mm512_mul_pd(_mm512_cvtepu64_pd(z), invp), _MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC);
        V q = _mm512_cvttpd_epu64(qd);
        r = _mm512_sub_epi64(z, _mm512_mullo_epi64(q, p));
        __mmask8 ng = _mm512_cmplt_epi64_mask(r, VZ);
        q = _mm512_mask_sub_epi64(q, ng, q, vset(1));
        r = _mm512_mask_add_epi64(r, ng, r, p);
        __mmask8 ge = _mm512_cmpge_epu64_mask(r, p);
        q = _mm512_mask_add_epi64(q, ge, q, vset(1));
        r = _mm512_mask_sub_epi64(r, ge, r, p);
        acc[k] = _mm512_mask_add_epi64(acc[k], lanes, acc[k], q);
    }
}

/* ============================ FAST primes: r = c * 2^(d-4) ============================ */
static void process_fast(const Config *cfg, Partial *o, const uint32_t *ps, const uint32_t *cs, int n, V acc[5]) {
    uint64_t t0 = __rdtsc();
    V p[NVF], pinv[NVF], p2[NVF], X[NVF], C[NVF]; __m512d invp[NVF]; __mmask8 lanes[NVF];
    for (int v = 0; v < NVF; v++) {
        uint64_t pl[8], cl[8]; int cnt = 0;
        for (int l = 0; l < 8; l++) {
            int i = v * 8 + l;
            if (i < n) { pl[l] = ps[i]; cl[l] = cs[i]; cnt++; } else { pl[l] = ps[0]; cl[l] = cs[0]; }
        }
        lanes[v] = (__mmask8)((1u << cnt) - 1);
        p[v] = _mm512_loadu_si512(pl); C[v] = _mm512_loadu_si512(cl);
        pinv[v] = vpinv(p[v]); p2[v] = _mm512_add_epi64(p[v], p[v]);
        invp[v] = _mm512_div_pd(_mm512_set1_pd(1.0), _mm512_cvtepu64_pd(p[v]));
        X[v] = vpow2small(cfg->t0f, p[v], invp[v]);
    }
    const uint64_t E = cfg->Ef;
    for (int i = cfg->Lf - 1; i >= 0; i--) {
#pragma GCC unroll 4
        for (int v = 0; v < NVF; v++) X[v] = mm(X[v], X[v], p[v], pinv[v]);
        if ((E >> i) & 1) {
#pragma GCC unroll 4
            for (int v = 0; v < NVF; v++) X[v] = vdbl(X[v], p2[v]);
        }
    }
    for (int v = 0; v < NVF; v++) {
        if (!lanes[v]) continue;
        V r = vred(mm(X[v], C[v], p[v], pinv[v]), p[v]);
        vfrac(o, r, p[v], invp[v], lanes[v], acc);
    }
    o->fast += n; o->rounded += n; o->modexp_sq += (uint64_t)NVF * 8 * cfg->Lf;
    o->tsc[T_FAST] += __rdtsc() - t0;
}

/* ============================ MEDIUM primes (vector fraction accumulation) ============================ */
static inline V vdivfloor(uint64_t M, V p, __m512d invp) {
    /* floor(M / p) exactly, M < 2^33 */
    V Mv = vset(M);
    __m512d q = _mm512_roundscale_pd(_mm512_mul_pd(_mm512_set1_pd((double)M), invp), _MM_FROUND_TO_NEG_INF | _MM_FROUND_NO_EXC);
    V u = _mm512_cvttpd_epu64(q);
    V pr = _mm512_mullo_epi64(u, p);
    __mmask8 big = _mm512_cmpgt_epu64_mask(pr, Mv);
    u = _mm512_mask_sub_epi64(u, big, u, vset(1)); pr = _mm512_mask_sub_epi64(pr, big, pr, p);
    __mmask8 sm = _mm512_cmple_epu64_mask(_mm512_add_epi64(pr, p), Mv);
    return _mm512_mask_add_epi64(u, sm, u, vset(1));
}
static inline V vcnt(V U) { /* U>=1 ? (U-1)/2+1 : 0  == (U+1)/2 */
    return _mm512_srli_epi64(_mm512_add_epi64(U, vset(1)), 1);
}


#define MEDLOOP(T0, T1, U2, U3, U4) \
    for (uint64_t t = (T0); t < (T1); t++) { \
        V tv = vset(t), u = vset(2 * t + 1); \
        _Pragma("GCC unroll 2") \
        for (int v = 0; v < NVM; v++) { \
            V p = P[v], pinv = PINV[v]; \
            __mmask8 act = _mm512_cmplt_epu64_mask(tv, C1[v]) & _mm512_test_epi64_mask(UM[v], UM[v]); \
            V t12 = W1[v], t34 = VZ; \
            if (U2) t12 = _mm512_mask_add_epi64(t12, _mm512_cmplt_epu64_mask(tv, C2[v]), t12, W2[v]); \
            if (U3) t34 = _mm512_maskz_mov_epi64(_mm512_cmplt_epu64_mask(tv, C3[v]), W3[v]); \
            if (U4) t34 = _mm512_mask_add_epi64(t34, _mm512_cmplt_epu64_mask(tv, C4[v]), t34, W4[v]); \
            __mmask8 n12 = _mm512_test_epi64_mask(_mm512_xor_si512(K[v], CHI[v]), vset(2)); \
            t12 = _mm512_mask_sub_epi64(t12, n12, P2[v], t12); \
            V val = t12; \
            if (U3) { __mmask8 n34 = _mm512_test_epi64_mask(K[v], vset(1)); \
                      t34 = _mm512_mask_sub_epi64(t34, n34, P2[v], t34); val = _mm512_add_epi64(t12, t34); } \
            V nn = mm2(N[v], u, val, D[v], p, pinv); \
            V dd = mm(D[v], u, p, pinv); \
            N[v] = _mm512_mask_mov_epi64(N[v], act, nn); \
            D[v] = _mm512_mask_mov_epi64(D[v], act, dd); \
            W1[v] = VSHR(W1[v], 3, vset(7)); \
            if (U2) W2[v] = VSHR(W2[v], 5, vset(31)); \
            if (U3) W3[v] = VSHR(W3[v], 6, vset(63)); \
            if (U4) W4[v] = VSHR(W4[v], 10, vset(1023)); \
            K[v] = _mm512_and_si512(_mm512_add_epi64(K[v], KS[v]), vset(3)); \
            V um = _mm512_add_epi64(UM[v], vset(2)); \
            UM[v] = _mm512_min_epu64(um, _mm512_sub_epi64(um, p)); \
        } \
    }

static void process_medium(const Config *cfg, Partial *o, const uint32_t *ps, int n, V acc[5]) {
    uint64_t t0 = __rdtsc();
    V P[NVM], PINV[NVM], P2[NVM], C1[NVM], C2[NVM], C3[NVM], C4[NVM], K[NVM], KS[NVM], CHI[NVM], UM[NVM];
    V W1[NVM], W2[NVM], W3[NVM], W4[NVM], N[NVM], D[NVM];
    __m512d INVP[NVM]; __mmask8 lanes[NVM];
    uint64_t maxc = 0;
    for (int v = 0; v < NVM; v++) {
        uint64_t pl[8]; int cnt = 0;
        for (int l = 0; l < 8; l++) { int i = v * 8 + l; if (i < n) { pl[l] = ps[i]; cnt++; } else pl[l] = ps[0]; }
        lanes[v] = (__mmask8)((1u << cnt) - 1);
        V p = _mm512_loadu_si512(pl);
        P[v] = p; PINV[v] = vpinv(p); P2[v] = _mm512_add_epi64(p, p);
        INVP[v] = _mm512_div_pd(_mm512_set1_pd(1.0), _mm512_cvtepu64_pd(p));
        C1[v] = vcnt(vdivfloor(cfg->M1, p, INVP[v]));
        C2[v] = vcnt(vdivfloor(cfg->M2, p, INVP[v]));
        C3[v] = vcnt(vdivfloor(cfg->M3, p, INVP[v]));
        C4[v] = vcnt(vdivfloor(cfg->M4, p, INVP[v]));
        uint64_t mc = (uint64_t)_mm512_mask_reduce_max_epu64(lanes[v], C1[v]);
        if (mc > maxc) maxc = mc;
        o->lane_iters_useful += (uint64_t)_mm512_mask_reduce_add_epi64(lanes[v], C1[v]);
        K[v] = _mm512_and_si512(_mm512_srli_epi64(_mm512_sub_epi64(p, vset(1)), 1), vset(3));
        KS[v] = _mm512_and_si512(p, vset(3));
        V p7 = _mm512_and_si512(p, vset(7));
        __mmask8 chin = _mm512_cmpeq_epi64_mask(p7, vset(3)) | _mm512_cmpeq_epi64_mask(p7, vset(5));
        CHI[v] = _mm512_maskz_mov_epi64(chin, vset(2));
        UM[v] = vset(1);
        W1[v] = vset(32); W2[v] = vset(8); W3[v] = vset(8); W4[v] = vset(1);
        N[v] = VZ; D[v] = vset(1);
    }
    o->lane_iters += maxc * 8 * NVM;
    uint64_t maxc2 = 0, maxc3 = 0, maxc4 = 0;
    for (int v = 0; v < NVM; v++) {
        uint64_t a = (uint64_t)_mm512_reduce_max_epu64(C2[v]), b = (uint64_t)_mm512_reduce_max_epu64(C3[v]), c = (uint64_t)_mm512_reduce_max_epu64(C4[v]);
        if (a > maxc2) { maxc2 = a; } if (b > maxc3) { maxc3 = b; } if (c > maxc4) { maxc4 = c; }
    }
    if (maxc2 > maxc) { maxc2 = maxc; } if (maxc3 > maxc2) { maxc3 = maxc2; } if (maxc4 > maxc3) { maxc4 = maxc3; }
    MEDLOOP(0, maxc4, 1, 1, 1)
    MEDLOOP(maxc4, maxc3, 1, 1, 0)
    MEDLOOP(maxc3, maxc2, 1, 0, 0)
    MEDLOOP(maxc2, maxc, 0, 0, 0)
    uint64_t t1 = __rdtsc();
    o->tsc[T_MEDLOOP] += t1 - t0;
    /* joint exponentiation X = 2^(Em+52) * (D/R)^(p-2), then r = mm(X, N) = 2^(d-4) N/D */
    V X[NVM], PM2[NVM];
    for (int v = 0; v < NVM; v++) {
        X[v] = vpow2small(cfg->t0m, P[v], INVP[v]);
        PM2[v] = _mm512_sub_epi64(P[v], vset(2));
        D[v] = vred(D[v], P[v]);
    }
    const uint64_t E = cfg->Em;
    /* 2-bit fixed window on the per-lane exponent p-2: Y_b = (D/R)^b * R */
    V D2[NVM], D3[NVM];
    for (int v = 0; v < NVM; v++) {
        D2[v] = mm(D[v], D[v], P[v], PINV[v]);
        D3[v] = mm(D2[v], D[v], P[v], PINV[v]);
    }
    int i = cfg->Lm - 1;
    if (cfg->Lm & 1) {   /* odd length: one single-bit step first */
        V bit = vset(1ULL << i);
        for (int v = 0; v < NVM; v++) {
            X[v] = mm(X[v], X[v], P[v], PINV[v]);
            if ((E >> i) & 1) X[v] = vdbl(X[v], P2[v]);
            __mmask8 b = _mm512_test_epi64_mask(PM2[v], bit);
            X[v] = _mm512_mask_mov_epi64(X[v], b, mm(X[v], D[v], P[v], PINV[v]));
        }
        i--;
    }
    for (; i >= 1; i -= 2) {
#pragma GCC unroll 2
        for (int v = 0; v < NVM; v++) {
            X[v] = mm(X[v], X[v], P[v], PINV[v]);
            if ((E >> i) & 1) X[v] = vdbl(X[v], P2[v]);
            X[v] = mm(X[v], X[v], P[v], PINV[v]);
            if ((E >> (i - 1)) & 1) X[v] = vdbl(X[v], P2[v]);
            V dig = _mm512_and_si512(_mm512_srli_epi64(PM2[v], (unsigned)(i - 1)), vset(3));
            __mmask8 b1 = _mm512_cmpeq_epi64_mask(dig, vset(1)), b2 = _mm512_cmpeq_epi64_mask(dig, vset(2));
            __mmask8 b3 = _mm512_cmpeq_epi64_mask(dig, vset(3));
            V Y = _mm512_mask_mov_epi64(_mm512_mask_mov_epi64(D3[v], b1, D[v]), b2, D2[v]);
            X[v] = _mm512_mask_mov_epi64(X[v], b1 | b2 | b3, mm(X[v], Y, P[v], PINV[v]));
        }
    }
    for (int v = 0; v < NVM; v++) {
        if (!lanes[v]) continue;
        V r = vred(mm(X[v], N[v], P[v], PINV[v]), P[v]);
        vfrac(o, r, P[v], INVP[v], lanes[v], acc);
    }
    o->medium += n; o->rounded += n; o->modexp_sq += (uint64_t)NVM * 8 * cfg->Lm;
    o->tsc[T_MEDEXP] += __rdtsc() - t1;
}

/* ============================ SCALAR: small primes & prime powers ============================ */
/* sum_{l<L} x^l mod q, division-free binary splitting */
static uint64_t sgeom(uint64_t x, uint64_t L, Mod m) {
    uint64_t S = 0, P = 1 % m.q;
    for (int i = 63 - (L ? __builtin_clzll(L) : 63); i >= 0 && L; i--) {
        S = smul(S, sadd(1 % m.q, P, m.q), m); P = smul(P, P, m);
        if ((L >> i) & 1) { S = sadd(S, P, m.q); P = smul(P, x, m); }
    }
    return S;
}
static inline bool sgn_neg(int j, unsigned k) { return j < 2 ? ((k >> 1) & 1) : (k & 1); }
/* G_j(c, I) = sum_{i<I} sigma_j(c+i) rho^i */
static uint64_t sG(int j, unsigned c, uint64_t I, uint64_t rho, Mod m) {
    uint64_t q = m.q;
    if (j >= 2) {
        uint64_t g = sgeom(sneg(rho, q), I, m);
        return (c & 1) ? sneg(g, q) : g;
    }
    uint64_t L = I >> 1, x = sneg(smul(rho, rho, m), q);
    uint64_t t0 = ((c >> 1) & 1) ? q - 1 : 1 % q;
    uint64_t t1 = (((c + 1) >> 1) & 1) ? q - 1 : 1 % q;
    uint64_t g = smul(sadd(t0, smul(t1, rho, m), q), sgeom(x, L, m), m);
    if (I & 1) g = sadd(g, smul(t0, spow(x, L, m), m), q);
    return g;
}

static void eval_scalar(const Config *cfg, Partial *o, uint64_t q, uint64_t p) {
    uint64_t ts = __rdtsc();
    Mod m = mod_init(q);
    static const int mj[4] = {3, 5, 6, 10};
    uint64_t U[4] = {cfg->M1 / q, cfg->M2 / q, cfg->M3 / q, cfg->M4 / q};
    uint64_t wh = sinv(spow2((q - 1) >> 1, m), q);
    uint64_t wq = smul(wh, wh, m); wq = (wq & 1) ? (wq + q) >> 1 : wq >> 1;  /* 2^-q */
    uint64_t c[4] = {32 % q, 8 % q, 8 % q, 1 % q};
    uint64_t init[4], step[4];
    for (int j = 0; j < 4; j++) { init[j] = smul(c[j], spow(wh, mj[j], m), m); step[j] = spow(wq, mj[j], m); }
    o->scalar_modexp += 2; o->scalar_inv += 1;
    unsigned k0 = (unsigned)(((q - 1) >> 1) & 3), ks = (unsigned)(q & 3);
    uint64_t count = ((U[0] - 1) >> 1) + 1;
    uint64_t A = 0;
    uint64_t bu[256], bpref[256], bval[256];
    if (2 * q < count) {
        /* residue-class block sums: u = u0 + 2q i, u0 odd in [1, 2q), p !| u0 */
        uint64_t Q[4], Rm[4], G[4][4][2], rho[4];
        for (int j = 0; j < 4; j++) {
            Q[j] = U[j] / (2 * q); Rm[j] = U[j] % (2 * q);
            rho[j] = spow(step[j], q, m);
            for (unsigned cc = 0; cc < 4; cc++)
                for (int f = 0; f < 2; f++)
                    G[j][cc][f] = smul(init[j], sG(j, cc, Q[j] + f, rho[j], m), m);
        }
        uint64_t w[4] = {1 % q, 1 % q, 1 % q, 1 % q};
        unsigned k = k0;
        uint64_t u0 = 1;
        while (u0 < 2 * q) {
            int nb = 0; uint64_t prod = 1 % q;
            while (u0 < 2 * q && nb < 256) {
                if (u0 % p) {
                    uint64_t val = 0;
                    for (int j = 0; j < 4; j++) val = sadd(val, smul(w[j], G[j][k][u0 <= Rm[j]], m), q);
                    uint64_t um = u0 >= q ? u0 - q : u0;
                    bu[nb] = um; bpref[nb] = prod; bval[nb] = val; prod = smul(prod, um, m); nb++;
                }
                for (int j = 0; j < 4; j++) w[j] = smul(w[j], step[j], m);
                k = (k + ks) & 3; u0 += 2; o->scalar_iters++;
            }
            if (nb) {
                uint64_t ip = sinv(prod, q); o->scalar_inv++;
                for (int i = nb - 1; i >= 0; i--) {
                    uint64_t iu = smul(ip, bpref[i], m); ip = smul(ip, bu[i], m);
                    A = sadd(A, smul(iu, bval[i], m), q);
                }
            }
        }
    } else {
        /* direct joint pass over t in [0, count) */
        uint64_t pw[4]; uint64_t cnt[4];
        for (int j = 0; j < 4; j++) { pw[j] = init[j]; cnt[j] = U[j] ? ((U[j] - 1) >> 1) + 1 : 0; }
        unsigned k = k0; uint64_t t = 0, um = 1 % q, up = 1 % p;
        while (t < count) {
            int nb = 0; uint64_t prod = 1 % q;
            while (t < count && nb < 256) {
                if (up) {
                    uint64_t val = 0;
                    for (int j = 0; j < 4; j++)
                        if (t < cnt[j]) val = sgn_neg(j, k) ? ssub(val, pw[j], q) : sadd(val, pw[j], q);
                    bu[nb] = um; bpref[nb] = prod; bval[nb] = val; prod = smul(prod, um, m); nb++;
                }
                for (int j = 0; j < 4; j++) pw[j] = smul(pw[j], step[j], m);
                k = (k + ks) & 3; um += 2; if (um >= q) um -= q; up += 2; if (up >= p) up -= p;
                t++; o->scalar_iters++;
            }
            if (nb) {
                uint64_t ip = sinv(prod, q); o->scalar_inv++;
                for (int i = nb - 1; i >= 0; i--) {
                    uint64_t iu = smul(ip, bpref[i], m); ip = smul(ip, bu[i], m);
                    A = sadd(A, smul(iu, bval[i], m), q);
                }
            }
        }
    }
    uint64_t r = smul(A, spow2((uint64_t)cfg->d - 4, m), m);
    o->scalar_modexp++;
    o->sum += fixed_fraction(r, q);
    o->rounded++;
    if (q == p) o->scal++; else o->pps++;
    o->tsc[T_SCALAR] += __rdtsc() - ts;
}

/* ============================ workers ============================ */
typedef struct {
    const Config *cfg;
    atomic_uint_fast64_t next_scalar, next_bvec, next_seg;
    uint64_t nscalar_tasks, nbvec;
} Job;
typedef struct { Job *job; Partial part; } Worker;

static inline uint32_t fast_coef(const Config *cfg, uint32_t p) {
    unsigned k0 = ((p - 1) >> 1) & 3;
    bool chin = ((p & 7) == 3) || ((p & 7) == 5);
    int t12 = 32 + (p <= cfg->M2 ? 8 : 0);
    int t34 = (p <= cfg->M3 ? 8 : 0) + (p <= cfg->M4 ? 1 : 0);
    int c = ((((k0 >> 1) & 1) != 0) ^ chin) ? -t12 : t12;
    c += (k0 & 1) ? -t34 : t34;
    return c < 0 ? (uint32_t)((int64_t)p + c) : (uint32_t)c;
}

static void *worker_fn(void *arg) {
    Worker *w = (Worker *)arg; Job *job = w->job; const Config *cfg = job->cfg; Partial *o = &w->part;
    V acc[5]; for (int k = 0; k < 5; k++) acc[k] = VZ;
    /* 1. scalar small primes (<= B0) and prime powers */
    for (;;) {
        uint64_t i = atomic_fetch_add_explicit(&job->next_scalar, 1, memory_order_relaxed);
        if (i >= job->nscalar_tasks) break;
        if (i < cfg->npp) eval_scalar(cfg, o, cfg->pp_q[i], cfg->pp_p[i]);
        else { uint32_t p = cfg->bp[i - cfg->npp]; eval_scalar(cfg, o, p, p); }
    }
    /* 2. base primes in (B0, B] as medium vectors */
    for (;;) {
        uint64_t i = atomic_fetch_add_explicit(&job->next_bvec, 1, memory_order_relaxed);
        if (i >= job->nbvec) break;
        uint64_t s = cfg->nsmall + i * 8 * NVM, e = s + 8 * NVM;
        if (e > cfg->nbp) e = cfg->nbp;
        process_medium(cfg, o, cfg->bp + s, (int)(e - s), acc);
    }
    /* 3. sieve segments */
    uint64_t *bits = aligned_alloc(64, SEGMAX / 8 + 64);
    uint32_t fp[8 * NVF], fc[8 * NVF], mp[8 * NVM]; int nf = 0, nm = 0;
    const uint64_t M1third = cfg->M1 / 3;
    for (;;) {
        uint64_t s = atomic_fetch_add_explicit(&job->next_seg, 1, memory_order_relaxed);
        if (s >= cfg->nseg) break;
        uint64_t ts = __rdtsc();
        uint64_t lo = cfg->seg_lo[s], hi = cfg->seg_lo[s + 1];   /* [lo, hi) odd indices, lo % 64 == 0 */
        if (hi > cfg->max_idx + 1) hi = cfg->max_idx + 1;
        uint64_t len = hi - lo, nw = (len + 63) >> 6;
        uint64_t wofs = (lo >> 6) % PRE_PERIOD;
        for (uint64_t i = 0; i < nw; i++) { bits[i] = cfg->pattern[wofs]; if (++wofs == PRE_PERIOD) wofs = 0; }
        uint64_t lo_val = 2 * lo + 1, hi_val = 2 * (hi - 1) + 1;
        for (int j = 0; j < 12; j++) {
            uint32_t p = cfg->wp[j], r = (uint32_t)(lo % p), st = 64 % p;
            const uint64_t *mk = cfg->wmask[j];
            for (uint64_t i = 0; i < nw; i++) { bits[i] |= mk[r]; r += st; if (r >= p) r -= p; }
        }
        for (uint32_t i = cfg->first_big; i < cfg->nbp; i++) {   /* 3..61 handled above */
            uint64_t p = cfg->bp[i];
            if (p * p > hi_val) break;
            uint64_t st;
            if (p * p >= lo_val) st = p * p;
            else {
                uint64_t qq = (uint64_t)((double)lo_val * cfg->bp_inv[i]);
                while (qq * p < lo_val) qq++;
                while (qq > 0 && (qq - 1) * p >= lo_val) qq--;
                if (!(qq & 1)) qq++;
                st = qq * p;
            }
            for (uint64_t idx = (st - lo_val) >> 1; idx < len; idx += p) bits[idx >> 6] |= 1ULL << (idx & 63);
        }
        if (len & 63) bits[nw - 1] |= ~0ULL << (len & 63);
        o->tsc[T_SIEVE] += __rdtsc() - ts;
        for (uint64_t wi = 0; wi < nw; wi++) {
            uint64_t x = ~bits[wi];
            while (x) {
                int b = __builtin_ctzll(x); x &= x - 1;
                uint32_t p = (uint32_t)(2 * (lo + wi * 64 + b) + 1);
                if (p <= cfg->B) continue;
                if (p > M1third) {
                    fp[nf] = p; fc[nf] = fast_coef(cfg, p);
                    if (++nf == 8 * NVF) { process_fast(cfg, o, fp, fc, nf, acc); nf = 0; }
                } else {
                    mp[nm] = p;
                    if (++nm == 8 * NVM) { process_medium(cfg, o, mp, nm, acc); nm = 0; }
                }
            }
        }
        if (nm) { process_medium(cfg, o, mp, nm, acc); nm = 0; }
    }
    if (nf) process_fast(cfg, o, fp, fc, nf, acc);
    free(bits);
    for (int k = 0; k < 5; k++) o->vacc[k] = (uint64_t)_mm512_reduce_add_epi64(acc[k]);
    return NULL;
}

/* ============================ setup ============================ */
static void build_base(Config *cfg) {
    uint64_t limit = (uint64_t)sqrt((double)cfg->M1) + 2;
    cfg->B = limit;
    uint8_t *comp = calloc(limit + 1, 1);
    cfg->bp = malloc((limit / 2 + 16) * sizeof(uint32_t)); cfg->nbp = 0;
    uint32_t cap = 1024; cfg->pp_q = malloc(cap * 4); cfg->pp_p = malloc(cap * 4); cfg->npp = 0;
    for (uint64_t p = 3; p <= limit; p += 2) {
        if (comp[p]) continue;
        cfg->bp[cfg->nbp++] = (uint32_t)p;
        for (uint64_t j = p * p; j <= limit; j += 2 * p) comp[j] = 1;
        for (uint64_t q = p * p; q <= cfg->M1; ) {
            if (cfg->npp == cap) { cap *= 2; cfg->pp_q = realloc(cfg->pp_q, cap * 4); cfg->pp_p = realloc(cfg->pp_p, cap * 4); }
            cfg->pp_q[cfg->npp] = (uint32_t)q; cfg->pp_p[cfg->npp] = (uint32_t)p; cfg->npp++;
            if (q > cfg->M1 / p) break;
            q *= p;
        }
    }
    free(comp);
    cfg->bp_inv = malloc(cfg->nbp * sizeof(double));
    for (uint32_t i = 0; i < cfg->nbp; i++) cfg->bp_inv[i] = 1.0 / (double)cfg->bp[i];
    /* sort prime powers by descending work estimate (small q first) for load balance */
    for (uint32_t i = 1; i < cfg->npp; i++) {
        uint32_t q = cfg->pp_q[i], p = cfg->pp_p[i]; int64_t j = (int64_t)i - 1;
        while (j >= 0 && cfg->pp_q[j] > q) { cfg->pp_q[j + 1] = cfg->pp_q[j]; cfg->pp_p[j + 1] = cfg->pp_p[j]; j--; }
        cfg->pp_q[j + 1] = q; cfg->pp_p[j + 1] = p;
    }
    static const uint32_t wps[12] = {17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61};
    for (int j = 0; j < 12; j++) {
        uint32_t p = wps[j], h = (p - 1) / 2; cfg->wp[j] = p;
        for (uint32_t r = 0; r < p; r++) {
            uint64_t mk = 0;
            for (int b = 0; b < 64; b++) if ((r + b) % p == h) mk |= 1ULL << b;
            cfg->wmask[j][r] = mk;
        }
    }
    cfg->first_big = 0; while (cfg->first_big < cfg->nbp && cfg->bp[cfg->first_big] <= 61) cfg->first_big++;
    cfg->pattern = malloc(PRE_PERIOD * 8);
    memset(cfg->pattern, 0, PRE_PERIOD * 8);
    static const unsigned pr[5] = {3, 5, 7, 11, 13};
    for (uint64_t i = 0; i < (uint64_t)PRE_PERIOD * 64; i++) {
        uint64_t v = 2 * i + 1;
        for (int k = 0; k < 5; k++) if (v % pr[k] == 0) { cfg->pattern[i >> 6] |= 1ULL << (i & 63); break; }
    }
}

static int bitlen(uint64_t x) { return x ? 64 - __builtin_clzll(x) : 0; }

static int parse_u64(const char *s, uint64_t lo, uint64_t hi, uint64_t *out) {
    if (!s || *s < '0' || *s > '9') return 0;
    char *end; errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno || *end || v < lo || v > hi) return 0;
    *out = v; return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s <n> [width=32] [threads=1]\n", argv[0]); return 2; }
    uint64_t n, w64 = 32, t64 = 1;
    if (!parse_u64(argv[1], 20000, UINT64_MAX / 4, &n) || (argc > 2 && !parse_u64(argv[2], 1, 64, &w64)) ||
        (argc > 3 && !parse_u64(argv[3], 1, 128, &t64)) || argc > 4) {
        fprintf(stderr, "usage: %s <n>=20000..> [width=1..64] [threads=1..128]\n", argv[0]);
        return 2;
    }
    unsigned width = (unsigned)w64, threads = (unsigned)t64;
    double b0frac = getenv("B0FRAC") ? atof(getenv("B0FRAC")) : 0.09;
    double segeps = getenv("SEGEPS") ? atof(getenv("SEGEPS")) : 0.01;

    Config cfg; memset(&cfg, 0, sizeof cfg);
    cfg.d = (int64_t)n - 1;
    cfg.M1 = 2 * ((cfg.d + 1) / 3) + 1;
    cfg.M2 = 2 * ((cfg.d - 1) / 5) + 1;
    cfg.M3 = 2 * ((cfg.d - 1) / 6) + 1;
    cfg.M4 = 2 * ((cfg.d - 4) / 10) + 1;
    if (cfg.M1 >= (1ULL << 32)) { fprintf(stderr, "M1 >= 2^32 unsupported\n"); return 2; }

    double start = wall_time(); uint64_t tsc_start = __rdtsc();
    build_base(&cfg);
    cfg.B0 = (uint64_t)(b0frac * sqrt((double)cfg.M1));
    if (cfg.B0 < 128) cfg.B0 = 128;
    while (cfg.nsmall < cfg.nbp && cfg.bp[cfg.nsmall] <= cfg.B0) cfg.nsmall++;

    cfg.Ef = (uint64_t)cfg.d - 4; cfg.Lf = bitlen(cfg.Ef) - 1; cfg.t0f = 52 + (cfg.Ef >> cfg.Lf);
    cfg.Em = (uint64_t)cfg.d - 56;
    cfg.Lm = bitlen(cfg.Em) - 1; if (cfg.Lm < bitlen(cfg.M1)) cfg.Lm = bitlen(cfg.M1);
    cfg.t0m = 52 + (cfg.Em >> cfg.Lm);

    /* segments in odd-index space: idx i <-> 2i+1; start just above B, aligned to 64 */
    cfg.max_idx = (cfg.M1 - 1) >> 1;
    uint64_t s0 = ((cfg.B + 1) >> 1) & ~63ULL;
    uint64_t cap = 1024; cfg.seg_lo = malloc(cap * 8); cfg.nseg = 0;
    for (uint64_t cur = s0; cur <= cfg.max_idx; ) {
        if (cfg.nseg + 2 >= cap) { cap *= 2; cfg.seg_lo = realloc(cfg.seg_lo, cap * 8); }
        cfg.seg_lo[cfg.nseg++] = cur;
        uint64_t step = (uint64_t)(segeps * (double)cur) & ~63ULL;
        if (step < 64) step = 64;
        if (step > SEGMAX) step = SEGMAX;
        cur += step;
    }
    cfg.seg_lo[cfg.nseg] = cfg.max_idx + 1 + 64;

    Job job; memset(&job, 0, sizeof job);
    job.cfg = &cfg;
    job.nscalar_tasks = cfg.npp + cfg.nsmall;
    job.nbvec = (cfg.nbp - cfg.nsmall + 8 * NVM - 1) / (8 * NVM);
    Worker *workers = aligned_alloc(64, sizeof(Worker) * threads);
    memset(workers, 0, sizeof(Worker) * threads);
    pthread_t *h = malloc(sizeof(pthread_t) * threads);
    for (unsigned i = 0; i < threads; i++) workers[i].job = &job;
    for (unsigned i = 1; i < threads; i++) pthread_create(&h[i], NULL, worker_fn, &workers[i]);
    worker_fn(&workers[0]);
    for (unsigned i = 1; i < threads; i++) pthread_join(h[i], NULL);

    Partial out; memset(&out, 0, sizeof out);
    u128 v100 = 0;
    for (unsigned i = 0; i < threads; i++) {
        Partial *w = &workers[i].part;
        out.sum += w->sum; out.rounded += w->rounded;
        for (int k = 0; k < 5; k++) v100 += (u128)w->vacc[k] << (20 * (4 - k));
        out.fast += w->fast; out.medium += w->medium; out.scal += w->scal; out.pps += w->pps;
        out.modexp_sq += w->modexp_sq; out.lane_iters += w->lane_iters; out.lane_iters_useful += w->lane_iters_useful;
        out.scalar_iters += w->scalar_iters; out.scalar_inv += w->scalar_inv; out.scalar_modexp += w->scalar_modexp;
        for (int k = 0; k < T_N; k++) out.tsc[k] += w->tsc[k];
    }
    v100 &= (((u128)1) << 100) - 1;
    out.sum += v100 >> 4;
    out.rounded += 1;   /* truncation of the 100-bit vector sum */

    /* exact tail (copied from euler_grouped.c) */
    {
        int64_t d = cfg.d;
#define TAIL(e, den, neg) do { int64_t sh = PRECISION + (e); u128 qv = 0; bool rem = true; \
        if (sh >= 0) { u128 num = (u128)1 << sh; qv = num / (den); rem = (qv * (den) != num); } \
        out.sum += (neg) ? -(qv + rem) : qv; out.rounded++; } while (0)
        int64_t k1 = (d + 1 >= 0) ? ((d + 1) / 3 + 1) : 0;
        for (int64_t k = k1; k < k1 + 36; k++) TAIL(d + 1 - 3 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
        int64_t k2 = (d - 1 >= 0) ? ((d - 1) / 5 + 1) : 0;
        for (int64_t k = k2; k < k2 + 24; k++) TAIL(d - 1 - 5 * k, (uint64_t)(2 * k + 1), ((k >> 1) & 1) != 0);
        int64_t k3 = (d - 1 >= 0) ? ((d - 1) / 6 + 1) : 0;
        for (int64_t k = k3; k < k3 + 20; k++) TAIL(d - 1 - 6 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
        int64_t k4 = (d - 4 >= 0) ? ((d - 4) / 10 + 1) : 0;
        for (int64_t k = k4; k < k4 + 14; k++) TAIL(d - 4 - 10 * k, (uint64_t)(2 * k + 1), (k & 1) != 0);
    }
    u128 lo = (out.sum - 1) & FIXED_MASK, hi = (out.sum + out.rounded + 1) & FIXED_MASK;
    uint64_t lw = (uint64_t)(lo >> (PRECISION - width)), hw = (uint64_t)(hi >> (PRECISION - width));
    bool certified = lw == hw;
    double seconds = wall_time() - start;
    double tps = (double)(__rdtsc() - tsc_start) / seconds;
    struct rusage ru; getrusage(RUSAGE_SELF, &ru);
    printf("{\"method\":\"euler_grouped_ifma\",\"n\":%" PRIu64 ",\"width\":%u,\"threads\":%u,\"certified\":%s,\"window\":",
           n, width, threads, certified ? "true" : "false");
    if (certified) { putchar('"'); for (unsigned i = width; i > 0; --i) putchar('0' + ((lw >> (i - 1)) & 1)); putchar('"'); }
    else fputs("null", stdout);
    uint64_t modexps = out.fast + out.medium + out.scalar_modexp;
    printf(",\"seconds\":%.6f,\"rss_bytes\":%" PRIu64 ",\"modexps\":%" PRIu64 ",\"fast\":%" PRIu64 ",\"medium\":%" PRIu64
           ",\"scalar_primes\":%" PRIu64 ",\"prime_powers\":%" PRIu64 ",\"fermat_inversions\":%" PRIu64
           ",\"euclid_inversions\":%" PRIu64 ",\"lane_sq\":%" PRIu64 ",\"lane_iters\":%" PRIu64 ",\"lane_iters_useful\":%" PRIu64
           ",\"scalar_iters\":%" PRIu64 ",\"rounded\":%" PRIu64 ",\"B\":%" PRIu64 ",\"B0\":%" PRIu64 ",\"segs\":%" PRIu64,
           seconds, (uint64_t)ru.ru_maxrss * 1024, modexps, out.fast, out.medium, out.scal, out.pps, out.medium,
           out.scalar_inv, out.modexp_sq, out.lane_iters, out.lane_iters_useful, out.scalar_iters, out.rounded,
           cfg.B, cfg.B0, cfg.nseg);
    static const char *nm[T_N] = {"sieve", "fast", "medloop", "medexp", "scalar"};
    printf(",\"cpu_s\":{");
    for (int k = 0; k < T_N; k++) printf("%s\"%s\":%.4f", k ? "," : "", nm[k], (double)out.tsc[k] / tps);
    printf("}}\n");
    return certified ? 0 : 1;
}

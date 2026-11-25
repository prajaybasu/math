#ifndef BELLARD_H
#define BELLARD_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef __uint128_t u128;

enum { PRECISION = 96, TAIL_ROWS = 11 };
#define FIXED_MASK (((u128)1 << PRECISION) - 1)

typedef struct {
    uint32_t stride, offset, shift;
    bool negative;
} Family;
extern const Family families[7];

typedef struct {
    uint64_t rounded, query_powers, coefficient_powers, query_squares, coefficient_squares;
    uint64_t mulmods, inversions, inverse_divisions, coefficient_slots;
    uint64_t block_sums, dyadic_divisions, primes, prime_powers, sieve_writes, phase_groups;
    uint64_t inversion_batches;
    double coefficient_seconds, evaluation_seconds, timer_seconds;
    double sieve_worker_seconds;
} Counts;

#ifdef COUNT_OPS
#define COUNT(counts, field, amount) ((counts)->field += (amount))
#else
#define COUNT(counts, field, amount) ((void)(counts))
#endif

typedef struct {
    u128 sum;
    Counts counts;
} Partial;

typedef struct {
    uint64_t reciprocal;
    uint32_t q;
} Mod;

static inline Mod modulus(uint32_t q)
{
    return (Mod){UINT64_MAX / q, q};
}

/* The reciprocal gives the quotient or one less for every uint64_t z. */
static inline uint32_t reduce(uint64_t z, Mod m)
{
    uint64_t quotient = ((u128)z * m.reciprocal) >> 64;
    uint64_t r = z - quotient * m.q;
    return r >= m.q ? r - m.q : r;
}

static inline uint32_t mulmod(uint32_t a, uint32_t b, Mod m, Counts *c)
{
    COUNT(c, mulmods, 1);
    return reduce((uint64_t)a * b, m);
}

static inline uint32_t addmod(uint32_t a, uint32_t b, uint32_t q)
{
    uint32_t s = a + b;
    return s >= q ? s - q : s;
}

static inline uint32_t submod(uint32_t a, uint32_t b, uint32_t q)
{
    return a >= b ? a - b : a + q - b;
}

static inline uint32_t negmod(uint32_t a, uint32_t q)
{
    return a ? q - a : 0;
}

/* Use a prefix of at most six exponent bits as a single shift. Appending
   each remaining bit needs one square, with any doubling before reduction. */
static inline uint32_t pow2mod(uint32_t e, Mod m, Counts *c, bool query)
{
    int remaining = e < 64 ? 0 : 26 - __builtin_clz(e);
#ifdef COUNT_OPS
    if (query) {
        ++c->query_powers;
        c->query_squares += remaining;
    } else {
        ++c->coefficient_powers;
        c->coefficient_squares += remaining;
    }
#else
    (void)c;
    (void)query;
#endif
    uint64_t r = reduce(UINT64_C(1) << (e >> remaining), m);
    while (remaining) {
        --remaining;
        r = reduce((r * r) << ((e >> remaining) & 1), m);
    }
    return (uint32_t)r;
}

static inline u128 fixed_fraction(uint32_t r, uint32_t q)
{
    uint64_t z = (uint64_t)r << 32;
    uint64_t a = z / q;
    z = (z - a * q) << 32;
    uint64_t b = z / q;
    z = (z - b * q) << 32;
    return ((u128)a << 64) | (b << 32) | (z / q);
}

static inline void accumulate(Partial *out, uint32_t r, uint32_t q)
{
    out->sum += fixed_fraction(r, q);
    ++out->counts.rounded;
}

typedef void (*Range)(const void *, uint32_t, uint32_t, Partial *, uint32_t *);

bool run_ranges(Range fn, const void *data, uint32_t length, uint32_t chunk,
                unsigned threads, size_t scratch, Partial *out);
double wall_time(void);
bool direct(uint32_t exponent, uint32_t last, unsigned threads, Partial *out);
bool grouped(uint32_t exponent, uint32_t last, unsigned threads, Partial *out,
             double *sieve_seconds);
#ifdef BELLARD_SEGMENTED
#define SEGMENTED_MAX_N UINT64_C(1000000000000)
enum { DEFAULT_COFACTOR_BLOCK = 1 << 16, MAX_COFACTOR_BLOCK = 1 << 20 };
bool grouped_segmented(uint64_t exponent, uint64_t last, unsigned threads,
                       size_t block_slots, Partial *out, double *sieve_seconds);
#endif

#endif

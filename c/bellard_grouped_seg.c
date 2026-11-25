#include "bellard.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint64_t q, reciprocal;
    unsigned shift;
} SegMod;

static inline SegMod seg_modulus(uint64_t q)
{
    if (q <= UINT32_MAX / 2)
        return (SegMod){q, modulus(q).reciprocal, 0};
    unsigned shift = 63 - __builtin_clzll(q);
    return (SegMod){q, ((u128)1 << (64 + shift)) / q, shift};
}

static inline uint64_t wide_reduce(u128 z, SegMod m)
{
    /* z < 2^(64 + shift), so the reciprocal quotient needs at most one correction. */
    uint64_t low_product = ((u128)(uint64_t)z * m.reciprocal) >> 64;
    uint64_t quotient = ((u128)(uint64_t)(z >> 64) * m.reciprocal + low_product) >> m.shift;
    uint64_t r = (uint64_t)(z - (u128)quotient * m.q);
    return r >= m.q ? r - m.q : r;
}

static inline uint64_t seg_mulmod(uint64_t a, uint64_t b, SegMod m, Counts *c)
{
    COUNT(c, mulmods, 1);
    if (!m.shift)
        return reduce(a * b, (Mod){m.reciprocal, m.q});
    return wide_reduce((u128)a * b, m);
}

static inline uint64_t seg_addmod(uint64_t a, uint64_t b, uint64_t q)
{
    uint64_t sum = a + b;
    return sum >= q ? sum - q : sum;
}

static inline uint64_t seg_submod(uint64_t a, uint64_t b, uint64_t q)
{
    return a >= b ? a - b : a + q - b;
}

static inline uint64_t seg_negmod(uint64_t a, uint64_t q)
{
    return a ? q - a : 0;
}

static inline uint64_t seg_pow2mod(uint64_t e, SegMod m, Counts *c, bool query)
{
    if (!m.shift && e <= UINT32_MAX)
        return pow2mod(e, (Mod){m.reciprocal, m.q}, c, query);

    unsigned remaining = e < 64 ? 0 : 58 - __builtin_clzll(e);
    if (query) {
        COUNT(c, query_powers, 1);
        COUNT(c, query_squares, remaining);
    } else {
        COUNT(c, coefficient_powers, 1);
        COUNT(c, coefficient_squares, remaining);
    }
    uint64_t seed = UINT64_C(1) << (e >> remaining);
    if (!m.shift) {
        Mod narrow = {m.reciprocal, m.q};
        uint64_t r = reduce(seed, narrow);
        while (remaining) {
            --remaining;
            r = reduce((r * r) << ((e >> remaining) & 1), narrow);
        }
        return r;
    }
    uint64_t r = wide_reduce(seed, m);
    while (remaining) {
        --remaining;
        r = wide_reduce(((u128)r * r) << ((e >> remaining) & 1), m);
    }
    return r;
}

static inline void seg_accumulate(Partial *out, uint64_t r, uint64_t q)
{
    if (q <= UINT32_MAX) {
        accumulate(out, r, q);
        return;
    }
    /* q has at most 40 bits. Four 24-bit quotient limbs fit in 64-bit divisions. */
    u128 fraction = 0;
    for (unsigned i = 0; i < 4; ++i) {
        uint64_t z = r << 24;
        uint64_t limb = z / q;
        fraction = (fraction << 24) | limb;
        r = z - limb * q;
    }
    out->sum += fraction;
    ++out->counts.rounded;
}

static uint64_t unit_inverse(uint64_t a, uint64_t modulus, Counts *c)
{
    COUNT(c, inversion_batches, 1);
    if (a == 1)
        return 1;
    COUNT(c, inversions, 1);
    uint64_t q = modulus;
    int64_t previous = 0, current = 1;
    while (a != 1) {
        int64_t quotient = q / a;
        uint64_t remainder = q - (uint64_t)quotient * a;
        int64_t next = previous - quotient * current;
        COUNT(c, inverse_divisions, 1);
        previous = current;
        current = next;
        q = a;
        a = remainder;
    }
    return current < 0 ? current + (int64_t)modulus : current;
}

static uint64_t power(uint64_t base, uint64_t exponent, SegMod m, Counts *c)
{
    uint64_t result = 1;
    while (exponent) {
        if (exponent & 1)
            result = seg_mulmod(result, base, m, c);
        exponent >>= 1;
        if (exponent)
            base = seg_mulmod(base, base, m, c);
    }
    return result;
}

typedef struct { uint64_t power, sum; } Geometry;

static Geometry geometric(uint64_t ratio, uint64_t length, SegMod m, Counts *c)
{
    COUNT(c, block_sums, 1);
    Geometry result = {1, 0};
    Geometry block = {ratio, 1};
    while (length) {
        if (length & 1) {
            result.sum = seg_addmod(result.sum, seg_mulmod(result.power, block.sum, m, c), m.q);
            result.power = seg_mulmod(result.power, block.power, m, c);
        }
        length >>= 1;
        if (length) {
            block.sum = seg_addmod(block.sum, seg_mulmod(block.power, block.sum, m, c), m.q);
            block.power = seg_mulmod(block.power, block.power, m, c);
        }
    }
    return result;
}

static uint64_t backwards(uint32_t lo, uint32_t hi, uint64_t first, uint32_t step,
                          uint32_t p, uint64_t z, SegMod m, uint64_t sum,
                          uint64_t *inverse, const uint64_t *prefix, Counts *c)
{
    for (uint32_t i = hi; i > lo;) {
        --i;
        uint64_t cofactor = first + (uint64_t)step * i;
        sum = seg_mulmod(sum, z, m, c);
        if (cofactor % p) {
            uint64_t value = seg_mulmod(*inverse, prefix[i], m, c);
            sum = seg_addmod(sum, value, m.q);
            *inverse = seg_mulmod(*inverse, cofactor, m, c);
        }
    }
    return sum;
}

static uint64_t family_coefficient(Family f, uint64_t last, uint32_t p, SegMod m,
                                   uint64_t z, uint64_t z5, uint64_t *prefix,
                                   uint32_t block_slots, Counts *c)
{
    uint64_t first, cofactor, step = m.q;
    uint32_t cofactor_step = f.stride;
    if (p == 5 && f.stride == 10) {
        if (f.offset != 5)
            return 0;
        /* 10k+5 = 5(2k+1), so the progression has step q/5. */
        step = m.q / 5;
        first = (step - 1) / 2;
        cofactor = 1;
        cofactor_step = 2;
        z = z5;
    } else {
        cofactor = 1;
        while (cofactor * m.q % f.stride != f.offset)
            cofactor += 2;
        if (cofactor * m.q < f.offset)
            cofactor += f.stride;
        first = (cofactor * m.q - f.offset) / f.stride;
    }
    if (first > last)
        return 0;

    uint64_t length = 1 + (last - first) / step;
    uint32_t slots = length < m.q ? length : m.q;
    uint32_t partial = length > m.q ? length % m.q : 0;
    COUNT(c, coefficient_slots, slots);
    uint64_t sum = 0, suffix = 0;
    for (uint32_t hi = slots; hi;) {
        uint32_t lo = hi > block_slots ? hi - block_slots : 0;
        uint32_t count = hi - lo;
        uint64_t block_first = cofactor + (uint64_t)cofactor_step * lo;
        uint64_t product = 1;
        for (uint32_t i = 0; i < count; ++i) {
            prefix[i] = product;
            uint64_t value = block_first + (uint64_t)cofactor_step * i;
            if (value % p)
                product = seg_mulmod(product, value, m, c);
        }
        uint64_t inverse = unit_inverse(product, m.q, c);
        /* Preserve the Horner state across blocks. Split it at the period's
           partial prefix while reusing the current block's inverse. */
        if (partial && lo <= partial && partial < hi) {
            suffix = backwards(partial - lo, count, block_first, cofactor_step,
                               p, z, m, sum, &inverse, prefix, c);
            sum = 0;
            count = partial - lo;
        }
        sum = backwards(0, count, block_first, cofactor_step, p, z, m, sum, &inverse, prefix, c);
        hi = lo;
    }
    if (length > m.q) {
        uint64_t front = partial ? sum : 0;
        uint64_t all = partial
            ? seg_addmod(front, seg_mulmod(power(z, partial, m, c), suffix, m, c), m.q)
            : sum;
        uint64_t ratio = p == m.q ? z : power(z, m.q, m, c);
        Geometry blocks = geometric(ratio, length / m.q, m, c);
        sum = seg_addmod(seg_mulmod(all, blocks.sum, m, c),
                         seg_mulmod(front, blocks.power, m, c), m.q);
    }
    if (!sum)
        return 0;
    uint64_t phi = m.q - m.q / p;
    uint64_t exponent = (f.shift + phi - (10 * first) % phi) % phi;
    uint64_t weight = seg_pow2mod(exponent, m, c, false);
    uint64_t result = seg_mulmod(sum, weight, m, c);
    return (f.negative ^ (first & 1)) ? seg_negmod(result, m.q) : result;
}

static uint64_t ratio_for_step(uint64_t step, uint64_t phi, SegMod m, Counts *c)
{
    uint64_t remainder = 10 * step % phi;
    return seg_negmod(seg_pow2mod(remainder ? phi - remainder : 0, m, c, false), m.q);
}

/* q_inverse is -q^-1 modulo 32. */
static inline uint64_t divide_pow2(uint64_t a, uint64_t q, uint32_t q_inverse, unsigned bits)
{
    uint32_t correction = ((uint32_t)a * q_inverse) & ((1u << bits) - 1);
    return (a + correction * q) >> bits;
}

static inline uint64_t weight10(uint64_t inverse, uint32_t phase, uint64_t p)
{
    static const int8_t signs[10] = {4, -4, -1, -4, 4, -4, 4, 1, 4, -4};
    int weight = signs[phase >> 1];
    if (weight == 4 || weight == -4) {
        inverse = seg_addmod(inverse, inverse, p);
        inverse = seg_addmod(inverse, inverse, p);
    }
    return weight < 0 ? seg_negmod(inverse, p) : inverse;
}

/* Every denominator is p(2i+1), and 2i+1 < p. The two slope-10 and
   slope-4 Horner ratios follow from 2^p=2 in F_p (see docs/method.md). */
static uint64_t sparse_prime(uint64_t x, uint64_t y, SegMod m, uint64_t *prefix,
                             uint32_t block_slots, Counts *c)
{
    uint64_t p = m.q;
    uint32_t hi = ((x / p + 1) >> 1) - 1;
    uint32_t length4 = (y / p + 1) >> 1;
    COUNT(c, coefficient_slots, hi + 1);
    uint32_t p20 = p % 20, p8 = p % 8;
    bool minus_chi = p8 == 3 || p8 == 5;
    uint64_t h10 = 0, h4 = 0;
    if (hi) {
        uint32_t low_p = p;
        uint32_t q_inverse = 0u - low_p * (2u - low_p * low_p);
        uint32_t phase = p20 * (2 * hi + 1) % 20;
        uint32_t step20 = (2 * p20) % 20;
        COUNT(c, dyadic_divisions, hi + 2 + (length4 ? length4 - 1 : 0));
        while (hi) {
            uint32_t lo = hi > block_slots ? hi - block_slots : 0;
            uint64_t product = 1;
            for (uint32_t i = lo; i < hi; ++i) {
                prefix[i - lo] = product;
                product = seg_mulmod(product, 2 * i + 3, m, c);
            }
            uint64_t inverse = unit_inverse(product, p, c);
            while (hi > lo) {
                uint32_t cofactor = 2 * hi + 1;
                --hi;
                uint64_t r = seg_mulmod(inverse, prefix[hi - lo], m, c);
                h10 = seg_addmod(divide_pow2(h10, p, q_inverse, 2), weight10(r, phase, p), p);
                if (hi + 1 < length4) {
                    uint64_t signed_r = (p8 * cofactor & 4) ? r : seg_negmod(r, p);
                    h4 = seg_addmod(divide_pow2(h4, p, q_inverse, 5), signed_r, p);
                }
                phase = phase >= step20 ? phase - step20 : phase + 20 - step20;
                inverse = seg_mulmod(inverse, cofactor, m, c);
            }
        }
        h10 = divide_pow2(h10, p, q_inverse, 2);
        h4 = divide_pow2(h4, p, q_inverse, 5);
    }
    h10 = seg_addmod(h10, weight10(1, p20, p), p);
    if (length4)
        h4 = (p8 & 4) ? seg_addmod(h4, 1, p) : seg_submod(h4, 1, p);
    h10 = seg_addmod(h10, h10, p);
    return minus_chi ? seg_submod(h10, h4, p) : seg_addmod(h10, h4, p);
}

typedef struct {
    uint64_t exponent, last, x, y;
    uint32_t root, segment_slots, block_slots, base_count;
    const uint32_t *base_primes;
} SegJob;

static void evaluate_prime(const SegJob *job, uint64_t p, uint64_t *prefix, Partial *out)
{
    Counts *c = &out->counts;
    SegMod m = seg_modulus(p);
    uint64_t coefficient = 0, exponent = job->exponent;
    if (p > job->root) {
        COUNT(c, prime_powers, 1);
        coefficient = sparse_prime(job->x, job->y, m, prefix, job->block_slots, c);
        exponent += 5;
    } else {
        for (uint64_t q = p;; q *= p) {
            COUNT(c, prime_powers, 1);
            if (q != p)
                m = seg_modulus(q);
            uint64_t phi = q - q / p;
            uint64_t z = ratio_for_step(q, phi, m, c);
            uint64_t z5 = p == 5 ? ratio_for_step(q / 5, phi, m, c) : 0;
            coefficient *= p;
            for (unsigned i = 0; i < 7; ++i) {
                uint64_t value = family_coefficient(families[i], job->last, p, m, z, z5,
                                                     prefix, job->block_slots, c);
                coefficient = seg_addmod(coefficient, value, q);
            }
            if (q * p > job->x)
                break;
        }
    }
    if (coefficient) {
        uint64_t residue = seg_pow2mod(exponent, m, c, true);
        seg_accumulate(out, seg_mulmod(coefficient, residue, m, c), m.q);
    }
}

/* This table ends at sqrt(x). Each worker marks and consumes one segment. */
static uint32_t *base_primes(uint32_t root, uint32_t *length)
{
    size_t slots = (root + 1) / 2;
    unsigned char *composite = calloc(slots, 1);
    uint32_t *primes = malloc(slots * sizeof(*primes));
    if (!composite || !primes) {
        free(composite);
        free(primes);
        return NULL;
    }
    uint32_t count = 0;
    for (uint32_t p = 3; p <= root; p += 2) {
        if (composite[p >> 1])
            continue;
        primes[count++] = p;
        if ((uint64_t)p * p <= root)
            for (uint32_t i = (p * p) >> 1; i < slots; i += p)
                composite[i] = 1;
    }
    free(composite);
    *length = count;
    return primes;
}

static void mark_segment(const SegJob *job, uint64_t first, uint32_t slots,
                         unsigned char *composite, Counts *c)
{
    memset(composite, 0, slots);
    uint64_t last = first + 2 * (uint64_t)(slots - 1);
    for (uint32_t j = 0; j < job->base_count; ++j) {
        uint32_t p = job->base_primes[j];
        uint64_t start = (uint64_t)p * p;
        if (start > last)
            break;
        if (start < first) {
            uint32_t stride = 2 * p;
            uint32_t remainder = (first - start) % stride;
            start = first + (remainder ? stride - remainder : 0);
        }
        for (uint32_t i = (start - first) / 2; i < slots; i += p) {
            composite[i] = 1;
            COUNT(c, sieve_writes, 1);
        }
    }
}

static void segment_range(const void *data, uint32_t start, uint32_t stop,
                          Partial *out, uint32_t *scratch)
{
    const SegJob *job = data;
    uint64_t *prefix = (uint64_t *)scratch;
    unsigned char *composite = (unsigned char *)(prefix + job->block_slots);
    for (uint32_t segment = start; segment < stop; ++segment) {
        uint64_t first = 3 + 2 * (uint64_t)segment * job->segment_slots;
        uint64_t remaining = (job->x - first) / 2 + 1;
        uint32_t slots = remaining < job->segment_slots ? remaining : job->segment_slots;
        double begin = wall_time();
        mark_segment(job, first, slots, composite, &out->counts);
        out->counts.sieve_worker_seconds += wall_time() - begin;
        for (uint32_t i = 0; i < slots; ++i) {
            if (!composite[i]) {
                COUNT(&out->counts, primes, 1);
                evaluate_prime(job, first + 2 * (uint64_t)i, prefix, out);
            }
        }
    }
}

bool grouped_segmented(uint64_t exponent, uint64_t last, unsigned threads,
                       size_t block_slots, Partial *out, double *sieve_seconds)
{
    uint64_t x = 10 * last + 9, y = 4 * last + 3;
    double start = wall_time();
    uint32_t root = sqrt((double)x);
    if ((uint64_t)root * root > x)
        --root;
    if ((uint64_t)(root + 1) * (root + 1) <= x)
        ++root;
    uint32_t base_count;
    uint32_t *primes = base_primes(root, &base_count);
    *sieve_seconds = wall_time() - start;
    if (!primes)
        return false;

    uint32_t segment_slots = root > 32768 ? root : 32768;
    /* A family scans at most min(q, 1 + x/q) slots. Sparse scans are shorter. */
    if (block_slots > root + 1)
        block_slots = root + 1;
    uint32_t segments = ((x - 1) / 2 + segment_slots - 1) / segment_slots;
    SegJob job = {exponent, last, x, y, root, segment_slots, block_slots, base_count, primes};
    /* run_ranges allocates in uint32_t words. Align each worker's prefix to uint64_t. */
    size_t sieve_words = (segment_slots + sizeof(uint64_t) - 1) / sizeof(uint64_t);
    size_t scratch = (block_slots + sieve_words) * sizeof(uint64_t) / sizeof(uint32_t);
    bool ok = run_ranges(segment_range, &job, segments, 1, threads, scratch, out);
    free(primes);
    return ok;
}

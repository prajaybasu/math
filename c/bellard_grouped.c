#include "bellard.h"

#include <math.h>
#include <stdlib.h>

static uint32_t unit_inverse(uint32_t a, uint32_t modulus, Counts *c)
{
    if (a == 1)
        return 1;
    COUNT(c, inversions, 1);
    uint32_t q = modulus;
    int64_t previous = 0, current = 1;
    while (a != 1) {
        uint32_t quotient = q / a;
        uint32_t remainder = q - quotient * a;
        int64_t next = previous - quotient * current;
        COUNT(c, inverse_divisions, 1);
        previous = current;
        current = next;
        q = a;
        a = remainder;
    }
    return current < 0 ? current + modulus : current;
}

static uint32_t power(uint32_t base, uint32_t exponent, Mod m, Counts *c)
{
    uint32_t result = 1;
    while (exponent) {
        if (exponent & 1)
            result = mulmod(result, base, m, c);
        exponent >>= 1;
        if (exponent)
            base = mulmod(base, base, m, c);
    }
    return result;
}

typedef struct { uint32_t power, sum; } Geometry;

static Geometry geometric(uint32_t ratio, uint32_t length, Mod m, Counts *c)
{
    COUNT(c, block_sums, 1);
    Geometry result = {1, 0};
    Geometry block = {ratio, 1};
    while (length) {
        if (length & 1) {
            result.sum = addmod(result.sum, mulmod(result.power, block.sum, m, c), m.q);
            result.power = mulmod(result.power, block.power, m, c);
        }
        length >>= 1;
        if (length) {
            block.sum = addmod(block.sum, mulmod(block.power, block.sum, m, c), m.q);
            block.power = mulmod(block.power, block.power, m, c);
        }
    }
    return result;
}

static uint32_t backwards(uint32_t lo, uint32_t hi, uint32_t first, uint32_t step,
                          uint32_t p, uint32_t z, Mod m, uint32_t *inverse,
                          const uint32_t *prefix, Counts *c)
{
    uint32_t sum = 0;
    for (uint32_t i = hi; i > lo;) {
        --i;
        uint32_t cofactor = first + step * i;
        sum = mulmod(sum, z, m, c);
        if (cofactor % p) {
            uint32_t residue = cofactor < m.q ? cofactor : cofactor % m.q;
            uint32_t next = mulmod(*inverse, prefix[i], m, c);
            sum = addmod(sum, next, m.q);
            *inverse = mulmod(*inverse, residue, m, c);
        }
    }
    return sum;
}

static uint32_t family_coefficient(Family f, uint32_t last, uint32_t p, Mod m,
                                   uint32_t z, uint32_t z5, uint32_t *prefix, Counts *c)
{
    uint32_t first, cofactor, step = m.q, cofactor_step = f.stride;
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
        while ((uint64_t)cofactor * m.q % f.stride != f.offset)
            cofactor += 2;
        if ((uint64_t)cofactor * m.q < f.offset)
            cofactor += f.stride;
        first = ((uint64_t)cofactor * m.q - f.offset) / f.stride;
    }
    if (first > last)
        return 0;

    uint32_t length = 1 + (last - first) / step;
    uint32_t slots = length < m.q ? length : m.q;
    COUNT(c, coefficient_slots, slots);
    uint32_t product = 1;
    for (uint32_t i = 0; i < slots; ++i) {
        prefix[i] = product;
        uint32_t value = cofactor + cofactor_step * i;
        if (value % p)
            product = mulmod(product, value, m, c);
    }
    uint32_t inverse = unit_inverse(product, m.q, c);
    uint32_t sum;
    if (length <= m.q) {
        sum = backwards(0, slots, cofactor, cofactor_step, p, z, m, &inverse, prefix, c);
    } else {
        uint32_t partial = length % m.q;
        uint32_t suffix = backwards(partial, slots, cofactor, cofactor_step, p, z,
                                    m, &inverse, prefix, c);
        uint32_t front = backwards(0, partial, cofactor, cofactor_step, p, z,
                                   m, &inverse, prefix, c);
        uint32_t all = addmod(front, mulmod(power(z, partial, m, c), suffix, m, c), m.q);
        uint32_t ratio = p == m.q ? z : power(z, m.q, m, c);
        Geometry blocks = geometric(ratio, length / m.q, m, c);
        sum = addmod(mulmod(all, blocks.sum, m, c), mulmod(front, blocks.power, m, c), m.q);
    }
    if (!sum)
        return 0;
    uint32_t phi = m.q - m.q / p;
    uint32_t exponent = (f.shift + (uint64_t)phi - (10 * (uint64_t)first) % phi) % phi;
    uint32_t weight = pow2mod(exponent, m, c, false);
    uint32_t result = mulmod(sum, weight, m, c);
    return (f.negative ^ (first & 1)) ? negmod(result, m.q) : result;
}

static uint32_t ratio_for_step(uint32_t step, uint32_t phi, Mod m, Counts *c)
{
    uint32_t remainder = 10 * (uint64_t)step % phi;
    return negmod(pow2mod(remainder ? phi - remainder : 0, m, c, false), m.q);
}

/* Divide in the residue field by 2^bits. q_inverse is -q^-1 modulo 32. */
static inline uint32_t divide_pow2(uint32_t a, uint32_t q, uint32_t q_inverse, unsigned bits)
{
    uint32_t correction = (a * q_inverse) & ((1u << bits) - 1);
    return (a + (uint64_t)correction * q) >> bits;
}

static inline uint32_t weight10(uint32_t inverse, uint32_t phase, uint32_t p)
{
    static const int8_t signs[10] = {4, -4, -1, -4, 4, -4, 4, 1, 4, -4};
    int weight = signs[phase >> 1];
    if (weight == 4 || weight == -4) {
        inverse = addmod(inverse, inverse, p);
        inverse = addmod(inverse, inverse, p);
    }
    return weight < 0 ? negmod(inverse, p) : inverse;
}

/* Every denominator is p(2i+1), and 2i+1 < p. The two slope-10 and
   slope-4 Horner ratios follow from 2^p=2 in F_p (see docs/method.md). */
static uint32_t sparse_prime(uint32_t x, uint32_t y, Mod m,
                             uint32_t *prefix, Counts *c)
{
    uint32_t p = m.q;
    uint32_t i = ((x / p + 1) >> 1) - 1;
    uint32_t length4 = (y / p + 1) >> 1;
    COUNT(c, coefficient_slots, i + 1);
    uint32_t p20 = p % 20, p8 = p % 8;
    bool minus_chi = p8 == 3 || p8 == 5;
    uint32_t h10 = 0, h4 = 0;
    if (i) {
        prefix[0] = 1;
        uint32_t product = 1;
        for (uint32_t j = 1; j <= i; ++j) {
            product = mulmod(product, 2 * j + 1, m, c);
            prefix[j] = product;
        }
        uint32_t inverse = unit_inverse(product, p, c);
        uint32_t q_inverse = 0u - p * (2u - p * p);
        uint32_t phase = p20 * (2 * i + 1) % 20;
        uint32_t step20 = (2 * p20) % 20;
        COUNT(c, dyadic_divisions, i + 2 + (length4 ? length4 - 1 : 0));
        while (i) {
            uint32_t r = mulmod(inverse, prefix[i - 1], m, c);
            h10 = addmod(divide_pow2(h10, p, q_inverse, 2), weight10(r, phase, p), p);
            if (i < length4) {
                uint32_t signed_r = (p8 * (2 * i + 1) & 4) ? r : negmod(r, p);
                h4 = addmod(divide_pow2(h4, p, q_inverse, 5), signed_r, p);
            }
            phase = phase >= step20 ? phase - step20 : phase + 20 - step20;
            inverse = mulmod(inverse, 2 * i + 1, m, c);
            --i;
        }
        h10 = divide_pow2(h10, p, q_inverse, 2);
        h4 = divide_pow2(h4, p, q_inverse, 5);
    }
    h10 = addmod(h10, weight10(1, p20, p), p);
    if (length4)
        h4 = (p8 & 4) ? addmod(h4, 1, p) : submod(h4, 1, p);
    h10 = addmod(h10, h10, p);
    return minus_chi ? submod(h10, h4, p) : addmod(h10, h4, p);
}

typedef struct {
    uint32_t exponent, last, x, y;
    const uint32_t *primes;
} GroupJob;

typedef struct { Mod m; uint32_t coefficient, exponent; } Group;

static Group prepare_group(const GroupJob *job, uint32_t p, uint32_t *prefix, Counts *c)
{
    Mod m = modulus(p);
    if ((uint64_t)p * p > job->x) {
        COUNT(c, prime_powers, 1);
        uint32_t coefficient = sparse_prime(job->x, job->y, m, prefix, c);
        return (Group){m, coefficient, job->exponent + 5};
    }

    uint32_t combined = 0;
    for (uint32_t q = p;; q *= p) {
        COUNT(c, prime_powers, 1);
        if (q != p)
            m = modulus(q);
        uint32_t phi = q - q / p;
        uint32_t z = ratio_for_step(q, phi, m, c);
        uint32_t z5 = p == 5 ? ratio_for_step(q / 5, phi, m, c) : 0;
        combined *= p;
        for (unsigned i = 0; i < 7; ++i) {
            uint32_t value = family_coefficient(families[i], job->last, p, m, z, z5, prefix, c);
            combined = addmod(combined, value, q);
        }
        if ((uint64_t)q * p > job->x)
            return (Group){m, combined, job->exponent};
    }
}

static inline void evaluate(Group g, Partial *out)
{
    if (g.coefficient) {
        uint32_t residue = pow2mod(g.exponent, g.m, &out->counts, true);
        accumulate(out, mulmod(g.coefficient, residue, g.m, &out->counts), g.m.q);
    }
}

static void group_range(const void *data, uint32_t start, uint32_t stop,
                        Partial *out, uint32_t *prefix)
{
    const GroupJob *job = data;
    for (uint32_t i = start; i < stop; ++i) {
#ifdef PROFILE_PHASES
        if ((i & 63) == 0) {
            double a = wall_time();
            Group g = prepare_group(job, job->primes[i], prefix, &out->counts);
            double b = wall_time();
            evaluate(g, out);
            double d = wall_time(), e = wall_time();
            ++out->counts.phase_groups;
            out->counts.coefficient_seconds += b - a;
            out->counts.evaluation_seconds += d - b;
            out->counts.timer_seconds += e - d;
            continue;
        }
#endif
        evaluate(prepare_group(job, job->primes[i], prefix, &out->counts), out);
    }
}

/* Odd-only Euler sieve. Each odd composite is written once, by its least
   prime factor, which fits in uint16_t for the supported range. */
static uint32_t *odd_primes(uint32_t x, uint32_t *length, Counts *c)
{
    uint16_t *least = calloc((x >> 1) + 1, sizeof(*least));
    size_t capacity = 1024;
    uint32_t *primes = malloc(capacity * sizeof(*primes));
    if (!least || !primes) {
        free(least);
        free(primes);
        return NULL;
    }
    uint32_t count = 0;
    for (uint32_t i = 3; i <= x; i += 2) {
        uint32_t smallest = least[i >> 1];
        if (!smallest) {
            if (count == capacity) {
                capacity += capacity / 2;
                uint32_t *more = realloc(primes, capacity * sizeof(*primes));
                if (!more) {
                    free(least);
                    free(primes);
                    return NULL;
                }
                primes = more;
            }
            primes[count++] = i;
            smallest = i;
        }
        uint32_t limit = x / i;
        if (limit > smallest)
            limit = smallest;
        for (uint32_t j = 0; j < count && primes[j] <= limit; ++j)
            least[(i * primes[j]) >> 1] = (uint16_t)primes[j];
    }
    free(least);
    *length = count;
    COUNT(c, primes, count);
    COUNT(c, sieve_writes, (x - 1) / 2 - count);
    return primes;
}

bool grouped(uint32_t exponent, uint32_t last, unsigned threads, Partial *out,
             double *sieve_seconds)
{
    uint32_t x = 10 * last + 9, y = 4 * last + 3, length;
    double start = wall_time();
    uint32_t *primes = odd_primes(x, &length, &out->counts);
    *sieve_seconds = wall_time() - start;
    if (!primes)
        return false;
    GroupJob job = {exponent, last, x, y, primes};
    size_t scratch = (size_t)sqrt(x) + 2;
    bool ok = run_ranges(group_range, &job, length, 256, threads, scratch, out);
    free(primes);
    return ok;
}

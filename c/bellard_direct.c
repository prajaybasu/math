#include "bellard.h"

static inline void term(Partial *out, uint32_t e, uint32_t q, bool negative)
{
    if (q == 1)
        return;
    uint32_t r = pow2mod(e, modulus(q), &out->counts, true);
    accumulate(out, negative ? negmod(r, q) : r, q);
}

static void direct_range(const void *data, uint32_t start, uint32_t stop,
                         Partial *out, uint32_t *scratch)
{
    (void)scratch;
    uint32_t exponent = *(const uint32_t *)data;
    for (uint32_t k = start; k < stop; ++k) {
        uint32_t e = exponent - 10 * k;
        bool odd = k & 1;
        term(out, e + 5, 4 * k + 1, !odd);
        term(out, e,     4 * k + 3, !odd);
        term(out, e + 8, 10 * k + 1, odd);
        term(out, e + 6, 10 * k + 3, !odd);
        term(out, e + 2, 10 * k + 5, !odd);
        term(out, e + 2, 10 * k + 7, !odd);
        term(out, e,     10 * k + 9, odd);
    }
}

bool direct(uint32_t exponent, uint32_t last, unsigned threads, Partial *out)
{
    return run_ranges(direct_range, &exponent, last + 1, 4096, threads, 0, out);
}

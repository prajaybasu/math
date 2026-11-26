/* Compute the four finite polylogarithms by FLINT multipoint evaluation at
   the integers 2,...,p-1, then test both local equations on each disc. */
#include <flint/nmod_poly.h>
#include <flint/ulong_extras.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static const ulong p = 1006003;
static ulong mul(ulong a, ulong b) { return (uint64_t)a * b % p; }
static ulong sub(ulong a, ulong b) { return (a + p - b) % p; }

static ulong det(const ulong x[3], const ulong y[3], const ulong z[3])
{
    ulong value = 0;
    for (int i = 0; i < 3; ++i) {
        int j = (i + 1) % 3, k = (i + 2) % 3;
        value += mul(x[i], sub(mul(y[j], z[k]), mul(y[k], z[j])));
    }
    return value % p;
}

int main(int argc, char **argv)
{
    if (argc != 2 || sizeof(ulong) < 8) {
        fprintf(stderr, "Usage on 64-bit FLINT: check_screen FIELD_TABLE\n");
        return 1;
    }
    FILE *file = fopen(argv[1], "wb");
    if (!file) { perror(argv[1]); return 1; }
    const slong count = (slong)p - 2;
    ulong *xs = flint_malloc(count * sizeof(*xs));
    ulong *inverse = flint_malloc(p * sizeof(*inverse));
    for (ulong a = 1; a < p; ++a) {
        inverse[a] = n_invmod(a, p);
        if (a >= 2) xs[a-2] = a;
    }
    nmod_poly_t poly;
    nmod_poly_init(poly, p);
    ulong *rows[4];
    for (int m = 1; m <= 4; ++m) {
        ulong *row = rows[m-1] = flint_calloc(p, sizeof(*row));
        for (ulong i = 1; i < p; ++i)
            nmod_poly_set_coeff_ui(poly, i, n_powmod2(inverse[i], m, p));
        nmod_poly_evaluate_nmod_vec_fast(row + 2, poly, xs, count);
        for (ulong a = 2; a < p; ++a) {
            ulong c = row[a] = mul(row[a], inverse[a-1]);
            unsigned char le[4] = {c & 255, (c >> 8) & 255, (c >> 16) & 255, 0};
            if (fwrite(le, 1, sizeof(le), file) != sizeof(le)) {
                perror("field table"); return 1;
            }
        }
    }
    if (fclose(file) != 0) { perror("field table"); return 1; }
    nmod_poly_clear(poly);
    flint_free(xs);
    /* log(b)/p^v = -(b^(p-1)-1)/p^v mod p at the first nonzero digit. */
    ulong q2 = n_powmod2(2, p-1, p*p) - 1;
    ulong q3 = n_powmod2(3, p-1, p*p*p) - 1;
    if (q2 % p || q3 % (p*p)) return 1;
    ulong ell2 = sub(0, q2 / p), ell3 = sub(0, q3 / (p*p));
    ulong *c1 = rows[0], *c2 = rows[1], *c3 = rows[2], *c4 = rows[3];
    if (!ell2 || !ell3 || !c2[3]) return 1;
    ulong special[2][3];
    for (int j = 0; j < 2; ++j) {
        ulong a = j == 0 ? 3 : 9, u = ((j + 1) * ell3) % p;
        special[j][0] = c4[a];
        special[j][1] = mul(u, c3[a]);
        special[j][2] = mul(n_powmod2(u, 3, p), c1[a]);
    }
    for (ulong a = 2; a < p; ++a) {
        if (!c2[a] && !c4[a]) printf("%lu one-one\n", a);
        if (!c1[a]) {
            printf("%lu singular\n", a);
            if (!c2[a]) printf("%lu unresolved\n", a);
            continue;
        }
        ulong u = mul(sub(0, mul(mul(ell2, ell3), c2[a])),
                      inverse[mul(c2[3], c1[a])]);
        ulong x[] = {c4[a], mul(u, c3[a]), mul(n_powmod2(u, 3, p), c1[a])};
        if (!det(x, special[0], special[1])) printf("%lu log-zero\n", a);
        ulong h = mul(a, inverse[sub(1, a)]);
        ulong L = mul(sub(0, c1[a]), inverse[h]);
        ulong Y2 = c2[a] + mul(c1[a], L) + mul(mul(h, inverse[2]), mul(L, L));
        if (!(Y2 % p)) printf("%lu li1-zero\n", a);
    }
    for (int i = 0; i < 4; ++i) flint_free(rows[i]);
    flint_free(inverse);
    return 0;
}

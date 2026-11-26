"""Compare resultant screens with exhaustive local root tests at small ordinary primes."""

from math import factorial

from sage.all import GF, QQ, PolynomialRing, ZZ
from certificate import centre_tables


def shifted(x, y, t):
    moments = [-x, *y]
    return [sum(moments[m - j] * t**j / factorial(j) for j in range(m + 1)) for m in range(1, 5)]


def equations(ring, coeffs):
    x, *y, t = ring.gens()
    w1, w2, w3, w4 = shifted(x, y, t)
    alpha, beta, a4, b4, c4 = coeffs
    return alpha * w2 + beta * t * w1, a4 * w4 + b4 * t * w3 + c4 * t**3 * w1


def coefficients(p, rows):
    field = GF(p)
    k, s = [field(-((pow(b, p - 1, p * p) - 1) // p)) for b in (2, 3)]
    assert k and s

    def values(a, t):
        y = [field((a - 1) * row[a % p]) for row in rows]
        return [v / (a - 1) for v in shifted(field(a), y, t)]

    w1, d, w3, w4 = values(3, s)
    v = (w4, s * w3, s**3 * w1)
    w1, _, w3, w4 = values(9, 2 * s)
    w = (w4, 2 * s * w3, (2 * s) ** 3 * w1)
    return [
        k * s,
        d,
        *(v[(j + 1) % 3] * w[(j + 2) % 3] - v[(j + 2) % 3] * w[(j + 1) % 3] for j in range(3)),
    ]


def ordinary(p):
    field = GF(p)
    ring = PolynomialRing(field, names="x,y1,y2,y3,y4,t")
    t = ring.gen(5)
    rows, _ = centre_tables(p)
    f, g = equations(ring, coefficients(p, rows))
    eliminant = f.resultant(g, t)
    assert eliminant and eliminant.total_degree() <= 6
    univar = PolynomialRing(field, "l")
    l = univar.gen()
    candidates, rational = set(), set()
    for a in range(2, p):
        coords = [field(a), *(field((a - 1) * row[a % p]) for row in rows)]
        if eliminant(*coords, 0) == 0:
            candidates.add(a)
        fl, gl = univar(f(*coords, l)), univar(g(*coords, l))
        if not fl and not gl:
            rational.add(a)
        elif fl.gcd(gl).roots(multiplicities=False):
            rational.add(a)
    assert rational <= candidates
    assert {(-3) % p, (-1) % p, 3 % p, 9 % p} <= rational
    print(
        f"{p}: resultant degree {eliminant.total_degree()}, "
        f"{len(rational)} discs with a common field root, {len(candidates)} resultant zeros"
    )


def bad_reduction(p):
    ring = PolynomialRing(QQ, names="x,y1,y2,y3,y4,t")
    x, *y, t = ring.gens()
    f, g = equations(ring, (p, 1, p, 0, 1))
    field = GF(p)
    mod = ring.change_ring(field)

    def reduce(poly):
        return mod({i: field(c) for i, c in poly.dict().items()})

    assert reduce(f).resultant(reduce(g), mod.gen(5)) == 0
    res = f.resultant(g, t)
    valuation = min(c.valuation(p) for c in res.coefficients())
    primitive = reduce(res / ZZ(p) ** valuation)
    assert valuation > 0 and primitive and primitive.total_degree() <= 6
    # At x=2, t=1 the prescribed W=(-p,1,0,1) is an exact common zero.
    coords = [QQ(2), *shifted(QQ(2), [-p, 1, 0, 1], QQ(-1))]
    assert f(*coords, 1) == g(*coords, 1) == 0
    assert primitive(*map(field, coords), 0) == 0
    print(f"{p}: vanishing naive resultant; primitive normalization removed p^{valuation}")


if __name__ == "__main__":
    for prime in (7, 13, 17, 29, 43, 101, 1009):
        ordinary(prime)
    bad_reduction(17)

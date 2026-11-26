"""Count discs for Example 4.1 of Balakrishnan et al. (arXiv:1805.03361).
Run with sage -python genus_three_discs.py. Coordinates X=4x, Y=64y.
"""

import argparse
import csv
import sys

from sage.all import GF, QQ, Qp, HyperellipticCurve, PolynomialRing, prime_range, vector


def screen(p, precision, depth):
    K = Qp(p, precision)
    F = GF(p)
    X = PolynomialRing(QQ, "x").gen()
    coeffs = [8, 32, 32, -16, -36, -8, 9, 4]
    f = sum(c * 4**6 * (X/4)**i for i, c in enumerate(coeffs))
    if not f.change_ring(F).is_squarefree():
        raise ValueError(f"Bad reduction at {p}")
    C = HyperellipticCurve(f.change_ring(K))

    def log_at(x, y):
        # The involution negates the integrals of holomorphic forms from infinity.
        return vector(C.coleman_integrals_on_basis(C(x, -y), C(x, y))[:3]) / 2

    v = log_at(K(-4), K(-64))
    v /= K(p)**min(c.valuation() for c in v)
    pivot = next(i for i in range(3) if v[i].valuation() == 0)

    def project(w):
        return vector([w[i] - v[i]*w[pivot]/v[pivot] for i in range(3) if i != pivot])

    def residue(z):
        if z.precision_absolute() < 1 or z.valuation() < 0:
            raise ArithmeticError("Unresolved residue")
        return F(z.residue())

    def classes(c, d, level):
        if any(z.precision_absolute() < level + 1 for z in c):
            raise ArithmeticError("Insufficient Coleman precision")
        if any(z.valuation() < level for z in c):
            return []
        a, b = [residue(z / p**level) for z in c]
        u, v = d
        if u or v:
            t = -a/u if u else -b/v
            return [int(t)] if b + v*t == 0 and a + u*t == 0 else []
        return list(range(p)) if a == b == 0 else []

    total = known = first = upper = 1  # Infinity is Weierstrass.
    surviving_pairs = []
    unresolved_pairs = []
    for a in F:
        x0 = int(a)
        f0 = f(x0)
        if F(f0) == 0:
            # The simple root lifts to a Weierstrass point with torsion image.
            total += 1
            known += 1
            first += 1
            upper += 1
            continue
        if not F(f0).is_square():
            continue
        total += 2
        x, y = K(x0), K(f0).sqrt()
        base = C(x, y)
        c = project(log_at(x, y))
        d = [residue(z) for z in project(vector(K, [1, x, x*x])/(2*y))]
        digits = classes(c, d, 1)
        # At X=0, Example 4.1 gives order 12 over Q(sqrt(2)); X=±4 are rational.
        witness = a in (F(0), F(4), F(-4))
        if witness and not digits:
            raise ArithmeticError("Screen excluded a known point")
        if not digits:
            continue
        first += 2
        surviving_pairs.append(x0)
        if witness:
            known += 2
            upper += 2
            continue
        offsets = [p*t for t in digits]
        for level in range(2, depth + 1):
            next_offsets = []
            for h in offsets:
                x1 = K(x0+h)
                y1 = K(f(x0+h)).sqrt()
                if residue(y1) != residue(y):
                    y1 = -y1
                delta = C.tiny_integrals_on_basis(base, C(x1, y1))
                c1 = c + project(vector(delta[:3]))
                next_offsets.extend(h + p**level*t for t in classes(c1, d, level))
            offsets = next_offsets
            if not offsets:
                break
        if offsets:
            upper += 2
            unresolved_pairs.append(x0)
    return (p, total, first, known, upper, " ".join(map(str, surviving_pairs)),
            " ".join(map(str, unresolved_pairs)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-prime", type=int, default=3)
    parser.add_argument("--max-prime", type=int, default=199)
    parser.add_argument("--precision", type=int, default=7)
    parser.add_argument("--depth", type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.depth < args.precision:
        parser.error("depth must be positive and below the working precision")
    out = csv.writer(sys.stdout, lineterminator="\n")
    out.writerow(("p", "all_discs", "first_digit_survivors", "occupied_lower",
                  "occupied_upper", "first_digit_x", "unresolved_x"))
    for prime in prime_range(args.min_prime, args.max_prime+1):
        out.writerow(screen(int(prime), args.precision, args.depth))
        sys.stdout.flush()

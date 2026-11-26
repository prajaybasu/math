"""Compute a global lift budget from finite polylogarithm polynomials."""

import argparse
from math import factorial

from sage.all import GF, PolynomialRing, ZZ


def budget(p):
    if p < 7 or not ZZ(p).is_prime():
        raise ValueError("The criterion requires a prime at least 7.")
    field = GF(p)
    k, s = [field(-((pow(i, p - 1, p**2) - 1) // p)) for i in (2, 3)]
    if bool(k) == bool(s):
        raise ValueError("Exactly one of the two logarithms must be exceptional.")
    ring = PolynomialRing(field, "x")
    x = ring.gen()
    # The product over all ordinary residue discs, each with multiplicity one.
    D = ring([1] * (p - 1))
    inv = [0, 1]
    for i in range(2, p):
        inv.append(-(p // i) * inv[p % i] % p)
    powers = inv
    polys = []
    for m in range(1, 5):
        polys.append(ring(powers))
        if m < 4:
            powers = [u * v % p for u, v in zip(powers, inv)]
    f1, f2, f3, f4 = polys

    def translated(values, a, L, m):
        # Return (a-1)Y_m(L), using finite polylogarithms at the disc centre.
        return sum(values[m - i - 1] * L**i / field(factorial(i)) for i in range(m)) - (
            a * L**m / field(factorial(m))
        )

    def anchor(a, j):
        values = [f(a) for f in polys]
        return [
            j**e * translated(values, a, j * s, m) / field(a - 1)
            for m, e in ((4, 0), (3, 1), (1, 3))
        ]

    v, w = anchor(3, 1), anchor(9, 2)
    A, B, C = [v[(i + 1) % 3] * w[(i + 2) % 3] - v[(i + 2) % 3] * w[(i + 1) % 3] for i in range(3)]
    d = translated([f(3) for f in polys], 3, s, 2) / field(2)
    print(f"p={p}  k,s,d,A,B,C mod p = {k},{s},{d},{A},{B},{C}")
    if not d:
        raise ValueError("The normalized dilogarithm at 3 must be a unit.")
    if not s:
        if not C:
            raise ValueError("The last cofactor must be a unit for the base-3 test.")
        H = (
            A * d**3 * ((f1 * f1) % D) * f4
            - B * k * d**2 * ((f1 * f2) % D) * f3
            - C * k**3 * ((f2 * f2) % D) * f2
        ) % D
        Q = (2 * x * f2 + f1 * f1) % D
    else:
        # The third anchor coordinates are exactly -k and -24k, including
        # the factor j^3. Remove k before reducing the first two cofactors.
        Aprime = v[1] * (-24) + w[1]
        Bprime = -w[0] + 24 * v[0]
        print(f"A/k,B/k mod p = {Aprime},{Bprime}")
        if not all((Aprime, Bprime, C)):
            print("At least one scaled cofactor has positive valuation.")
        # After cancellation the determinant is s²d A'Y4 + sd B' L Y3 - C L²Y2.
        L = (f1 * x.inverse_mod(D)) % D
        H = s**2 * d * Aprime * f4
        Q = (
            s**2 * d * Aprime * translated(polys, x, L, 4)
            + s * d * Bprime * L * translated(polys, x, L, 3)
            - C * L**2 * translated(polys, x, L, 2)
        ) % D
    # Keep degree < p through the extended Euclidean algorithm.
    T = (H * Q) % D
    W, U, V = D.xgcd(T)
    log_branch, li1_branch = D.gcd(H), D.gcd(Q)
    if W != U * D + V * T or W != log_branch.lcm(li1_branch).monic():
        raise ArithmeticError("The polynomial witness failed.")
    one_one = D.gcd(f2).gcd(f4).monic()
    singular = W.gcd(f1)
    template = (
        (x + 3) * (x + 1) * (x - 2) * (x - 3) * (x - 9) * (3 * x + 1) * (3 * x - 1) * (9 * x - 1)
    )
    quotient, remainder = template.quo_rem(W)
    if not remainder and quotient * (U * D + V * T) != template:
        raise ArithmeticError("The degree-eight witness failed.")
    roots = sorted(int(a) for a in W.roots(multiplicities=False))
    others = sorted(int(a) for a in one_one.roots(multiplicities=False))
    if len(roots) != W.degree() or len(others) != one_one.degree():
        raise ArithmeticError("The disc factors did not split into distinct linear factors.")
    print(
        f"p={p}  gcd degrees H,Q,union,(1,1) = "
        f"{log_branch.degree()},{li1_branch.degree()},{W.degree()},{one_one.degree()}"
    )
    print(f"(1,0) discs {roots}" if len(roots) <= 32 else f"(1,0) candidate discs: {len(roots)}")
    print(f"Unresolved singular discs: {singular.degree()}")
    print(f"All candidates lie in the eight rational residue classes: {not remainder}")
    if singular.degree() == 0:
        print(f"Simple depth-two root classes to examine: {2 * len(roots)}")
    print(f"(1,1) residues {others}")
    return roots, others


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int)
    budget(parser.parse_args().prime)

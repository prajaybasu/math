"""Compute a global lift budget from finite polylogarithm polynomials."""

import argparse

from sage.all import GF, PolynomialRing, ZZ


def budget(p):
    if p < 7 or not ZZ(p).is_prime():
        raise ValueError("The criterion requires a prime at least 7.")
    if pow(3, p - 1, p**2) != 1 or pow(2, p - 1, p**2) == 1:
        raise ValueError("The logarithm of 3 must be exceptional and that of 2 ordinary.")
    field = GF(p)
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

    def anchor(a, j):
        denominator = field(a - 1)
        return (f4(a) / denominator, j * f3(a) / denominator, j**3 * f1(a) / denominator)

    v, w = anchor(3, 1), anchor(9, 2)
    A, B, C = [v[(i + 1) % 3] * w[(i + 2) % 3] - v[(i + 2) % 3] * w[(i + 1) % 3] for i in range(3)]
    k = field(-((pow(2, p - 1, p**2) - 1) // p))
    d = f2(3) / field(2)
    if not all((k, d, C)):
        raise ValueError("The unit tests for k, d and C must pass.")

    H = (
        A * d**3 * ((f1 * f1) % D) * f4
        - B * k * d**2 * ((f1 * f2) % D) * f3
        - C * k**3 * ((f2 * f2) % D) * f2
    ) % D
    Q = (2 * x * f2 + f1 * f1) % D
    # Keep degree < p through the extended Euclidean algorithm.
    T = (H * Q) % D
    W, U, V = D.xgcd(T)
    log_branch, li1_branch = D.gcd(H), D.gcd(Q)
    if W != U * D + V * T or W != log_branch.lcm(li1_branch).monic():
        raise ArithmeticError("The polynomial witness failed.")
    one_one = D.gcd(f2).gcd(f4).monic()
    singular = D.gcd(f1).gcd(f2)
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
    print(f"(1,0) discs {roots}")
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

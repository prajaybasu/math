"""Exact ranks and kernel checks for truncated mixed finite polylogarithms."""

import argparse
from itertools import combinations_with_replacement
from math import comb

from sage.all import (
    GF, QQ, ZZ, PolynomialRing, is_prime, lcm, matrix, next_prime, previous_prime, prime_range,
)


def dimension(t):
    return (t**2 + 1) * comb(t + 4, 4)


def rank_test(p, t):
    """Return dimension and rank, verifying a kernel element if rank is submaximal."""
    if not is_prime(p) or t < 1:
        raise ValueError("p must be prime and t must be positive")
    field = GF(p)
    ring = PolynomialRing(field, "x")
    x = ring.gen()
    inverses = [field(j) ** -1 for j in range(1, p)]
    polylogs = {k: ring([0, *(v**k for v in inverses)]) for k in range(1, 5)}
    size = dimension(t)
    coeff_matrix = matrix(field, size, p, sparse=False)
    monomials = []
    for d in range(t + 1):
        for indices in combinations_with_replacement(range(1, 5), d):
            product = ring.one()
            for k in indices:
                product = (product * polylogs[k]).truncate(p)
            coeffs = product.padded_list(p)
            for j in range(t**2 + 1):
                if j < p:
                    coeff_matrix.set_row(len(monomials), [0] * j + coeffs[: p - j])
                monomials.append((j, indices))

    rank = coeff_matrix.rank()
    if rank < min(size, p):
        # A left-kernel vector gives coefficients in the original monomial basis.
        relation = coeff_matrix.left_kernel().basis()[0]
        total = ring.zero()
        terms = []
        for c, (j, indices) in zip(relation, monomials):
            if c:
                term = c * x**j
                for k in indices:
                    term = (term * polylogs[k]).truncate(p)
                total += term
                terms.append((int(c), j, indices))
        assert terms and total.truncate(p) == 0
        print(f"verified kernel example (coefficient, X-degree, weights): {terms}", flush=True)
    return size, rank


def boundary_primes(t, neighbors):
    size = dimension(t)
    lower = upper = size
    primes = []
    for _ in range(neighbors):
        if lower > 2:
            lower = int(previous_prime(lower))
            primes.append(lower)
        upper = int(next_prime(upper))
        primes.append(upper)
    return sorted(primes)


def certify_all_primes(t):
    """Use rational Taylor coefficients to certify every prime above the dimension."""
    size = dimension(t)
    shifts = t**2 + 1
    ring = PolynomialRing(QQ, "x")
    polylogs = [
        ring([0, *(QQ(1) / j**k for j in range(1, size + 1))]) for k in range(1, 5)
    ]
    # Coefficient indices 0..shifts-1 pivot on 1, X, ..., X^(shifts-1).
    # Each of two square minors completes those pivots with consecutive indices.
    columns = [[] for _ in range(shifts, size + 1)]
    for d in range(1, t + 1):
        for indices in combinations_with_replacement(range(4), d):
            product = ring.one()
            for k in indices:
                product = (product * polylogs[k]).truncate(size + 1)
            coeffs = product.padded_list(size + 1)
            for j in range(shifts):
                for i, column in enumerate(columns, start=shifts):
                    column.append(coeffs[i - j])
    int_columns = []
    for column in columns:
        denominator = lcm(c.denominator() for c in column)
        int_columns.append([ZZ(c * denominator) for c in column])
    dets = []
    for i, block in enumerate((int_columns[:-1], int_columns[1:])):
        det = matrix(ZZ, block).determinant(algorithm="flint")
        dets.append(det)
        print(f"t={t}, integer minor {i}: {det.nbits()} bits", flush=True)
    if t == 2:
        # At 109 the degree-75 coefficient restores the missing rank.
        assert dets[0] % 109 == 0 and dets[1] % 109 != 0
    common = dets[0].gcd(dets[1])
    if common == 0:
        raise ArithmeticError("both minors vanish over the rationals")
    for p in prime_range(size + 1):
        common = common.prime_to_m_part(p)
    print(f"t={t}, dimension={size}, determinant_bits={[v.nbits() for v in dets]}, "
          f"residual_gcd_bits={common.nbits()}", flush=True)
    if common != 1:
        raise ArithmeticError("these minors leave possible exceptional primes")
    print(f"t={t}: certified injective for every prime p > {size}", flush=True)
    small_primes = list(prime_range(size + 1))
    for p in small_primes:
        _, rank = rank_test(int(p), t)
        if rank != p:
            raise ArithmeticError(f"unexpected rank {rank} at p={p}, t={t}")
    print(f"t={t}: checked surjectivity at all {len(small_primes)} smaller primes", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--certify", type=int, nargs="+", metavar="T",
        help="verify maximal rank at every prime using integer minors and direct checks",
    )
    mode.add_argument(
        "--ceiling", type=int, nargs="+", metavar="T",
        help="test the primes bracketing the source dimension",
    )
    parser.add_argument(
        "--neighbors", type=int, default=1,
        help="number of primes to include on each side (default 1)",
    )
    args = parser.parse_args()
    if args.neighbors < 1 or any(t < 1 for t in (args.ceiling or args.certify or [])):
        parser.error("depths and neighbor count must be positive")
    if args.certify:
        for t in args.certify:
            certify_all_primes(t)
        raise SystemExit(0)
    cases = [(101, 2), (563, 3), (1213, 4)] if not args.ceiling else (
        (p, t) for t in args.ceiling for p in boundary_primes(t, args.neighbors)
    )
    for p, t in cases:
        size, rank = rank_test(p, t)
        print(f"p={p}, t={t}, dimension={size}, rank={rank}, "
              f"nullity={size-rank}, excess_nullity={min(size, p)-rank}", flush=True)

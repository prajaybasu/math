"""Check truncated mixed finite-polylogarithm substitution by exact matrix rank."""

from itertools import combinations_with_replacement

from sage.all import GF, PolynomialRing, matrix


def rank_test(p, t):
    field = GF(p)
    ring = PolynomialRing(field, "x")
    weights = range(1, 5)
    powers = [field(j) ** -1 for j in range(1, p)]
    polylogs = {k: ring([0, *(v**k for v in powers)]) for k in weights}
    rows = []
    for degree in range(t + 1):
        for indices in combinations_with_replacement(weights, degree):
            product = ring.one()
            for k in indices:
                product = (product * polylogs[k]).truncate(p)
            coeffs = product.padded_list(p)
            for j in range(t**2 + 1):
                rows.append([0] * j + coeffs[: p - j])
    rank = matrix(field, rows).rank()
    return len(rows), rank


if __name__ == "__main__":
    for p, t in [(101, 2), (563, 3), (1213, 4)]:
        size, rank = rank_test(p, t)
        print(f"p={p}, t={t}, dimension={size}, rank={rank}, nullity={size-rank}", flush=True)

"""Check the two depth-four refined components at either Wolstenholme prime."""

import argparse
import struct
from pathlib import Path

import sage.all as sage
from certificate import centre_tables, evaluate, local_tables, sparse_tables


def compare_tables(p, rows, path):
    with path.open("rb") as stream:
        for m, row in enumerate(rows, 1):
            buf = stream.read(4 * (p - 2))
            if len(buf) != 4 * (p - 2):
                raise ValueError("Incomplete field table")
            for a, (val,) in enumerate(struct.iter_unpack("<I", buf), 2):
                if val != row[a]:
                    raise ValueError(f"Field values differ at weight {m}, residue {a}")
        if stream.read(1):
            raise ValueError("Unexpected trailing field data")
    print(f"Matched {4 * (p - 2)} field entries.")


def screen(p, field_table):
    rows, inv = centre_tables(p)
    if field_table:
        compare_tables(p, rows, field_table)
    c1, c2, c3, c4 = rows
    k, s = [(-((pow(b, p - 1, p * p) - 1) // p)) % p for b in (2, 3)]

    def translated(a, L):
        # Y_m at log(z)/p = L, Taylor expanded about the Teichmüller centre.
        h = -a * inv[a - 1] % p
        return (
            (c1[a] + h * L) % p,
            (c2[a] + c1[a] * L + h * L**2 * inv[2]) % p,
            (c3[a] + c2[a] * L + c1[a] * L**2 * inv[2] + h * L**3 * inv[6]) % p,
            (c4[a] + c3[a] * L + c2[a] * L**2 * inv[2] + c1[a] * L**3 * inv[6] + h * L**4 * inv[24])
            % p,
        )

    y1, d, y3, y4 = translated(3, s)
    v = (y4, y3, y1)
    y1, _, y3, y4 = translated(9, 2 * s % p)
    w = (y4, 2 * y3, 8 * y1)
    A, B, C = [
        (v[(i + 1) % 3] * w[(i + 2) % 3] - v[(i + 2) % 3] * w[(i + 1) % 3]) % p for i in range(3)
    ]
    assert p % 4 == 3 and sage.ZZ(p).is_prime()
    assert k and s and d and A == 0 and B and C and c3[p - 1] == 0
    ks = k * s % p
    num_roots = 0
    candidates = []
    for a in range(2, p):
        h = -a * inv[a - 1] % p
        u = h * (ks * inv[2] + d) % p
        v = c1[a] * (ks + d) % p
        w = ks * c2[a] % p
        assert u != 0
        discriminant = (v * v - 4 * u * w) % p
        root = pow(discriminant, (p + 1) // 4, p)
        if root * root % p != discriminant:
            continue
        for sign in (1, -1) if root else (1,):
            L = (-v + sign * root) * inv[2 * u % p] % p
            num_roots += 1
            y1 = (c1[a] + h * L) % p
            y3 = (c3[a] + c2[a] * L + c1[a] * L**2 * inv[2] + h * L**3 * inv[6]) % p
            if (s * s * B * L * y3 + C * L**3 * y1) % p == 0:
                assert (u * L * L + v * L + w) % p == 0
                if (2 * u * L + v) % p == 0:
                    raise ArithmeticError(f"Singular common class at residue {a}, L={L}")
                candidates.append((a, L))
    one_one = [a for a in range(2, p) if c2[a] == c4[a] == 0]
    assert one_one == [p - 1]
    expected_points = (-3, -1, 2, 3, 9)
    residues = {x % p for x in expected_points}
    assert len(candidates) == len(residues) and {a for a, _ in candidates} == residues
    print(f"p={p}: {p - 2} discs, {num_roots} depth-two classes")
    print(f"Simple common classes (a,L): {sorted(candidates)}; (1,1) residues: {one_one}")
    return dict(candidates), {a: tuple(row[a] for row in rows) for a in residues}


def check_lifts(p, r, candidates, centres):
    n = 24
    assert 3 <= r <= 12 and n + 4 <= p
    points = (-3, -1, 2, 3, 9)
    vals = {}
    # Separate batches keep the large-prime power tables bounded in memory.
    for batch in ((2, 3, 9), (-3, -1)):
        residues = [x % p for x in batch]
        table = sparse_tables(p, r, residues)
        discs = local_tables(p, r, n, table)
        for x in batch:
            a = x % p
            assert tuple(-t % p for t in table[a]) == centres[a]
            zeta, log, li = discs[a]
            t = (x - zeta) / p
            vals[x] = [evaluate(f, t).add_bigoh(n) for f in (log, *li[1:])]
            assert int((vals[x][0] / p).residue()) == candidates[a]

    log2, log3 = vals[2][0], vals[3][0]

    def row(x):
        log, li1, _, li3, li4 = vals[x]
        return (li4, log * li3, log**3 * li1)

    for x in points:
        log, li1, li2, _, _ = vals[x]
        f2 = log2 * log3 * li2 + vals[3][2] * log * li1
        assert f2.precision_absolute() >= 5 and f2 == 0
        f4 = sage.matrix([row(x), row(3), row(9)]).det()
        if x == 2:
            v = int(f4.valuation())
            assert f4 != 0 and f4.precision_absolute() > v
            print(
                f"At 2: raw v(f4)={v}, first nonzero digit={int((f4 / p**v).residue())}, "
                f"absolute precision={int(f4.precision_absolute())}"
            )
        else:
            assert f4 == 0 and f4.precision_absolute() >= 14
    print("(1,0) = {-3,-1,3,9}; (1,1) = {-1}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prime", type=int, choices=(16843, 2124679))
    parser.add_argument("--digits", type=int, default=8, choices=range(3, 13))
    parser.add_argument(
        "--field-table", type=Path, help="compare an independently evaluated field table"
    )
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Certificate checks require assertions enabled.")
    candidates, centres = screen(args.prime, args.field_table)
    check_lifts(args.prime, args.digits, candidates, centres)

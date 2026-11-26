"""Check both depth-four components for S={2,3} at p=1006003.

Run with sage -python certificate.py --digits 6. The digits parameter
is the absolute precision of the depleted polylogarithms on surviving discs.
The sieve itself uses four finite polylogarithms over the prime field.
"""

import argparse
import json
import struct
import subprocess
import tempfile
from math import comb
from pathlib import Path
from random import Random
from time import perf_counter

import sage.all as s


def check_field_table(executable, p, rows, survivors):
    """Compare every residue and each sieve outcome with a subproduct-tree evaluation."""
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "field.bin"
        result = subprocess.run(
            [str(executable.resolve()), str(path)], check=True, stdout=subprocess.PIPE, text=True
        )
        field_row_size = 4 * (p - 2)
        with path.open("rb") as stream:
            for weight, row in enumerate(rows, 1):
                data = stream.read(field_row_size)
                if len(data) != field_row_size:
                    raise ValueError(f"Incomplete field table at weight {weight}")
                for a, (value,) in enumerate(struct.iter_unpack("<I", data), 2):
                    if row[a] != value:
                        raise ValueError(f"Field table mismatch at weight {weight}, disc {a}")
            assert not stream.read(1)
    expected = sorted(f"{a} {name}" for name, discs in survivors.items() for a in discs)
    assert sorted(result.stdout.splitlines()) == expected, "Sieve classifications differ"
    print(f"Matched {4 * (p - 2)} field entries and all sieve classifications.")


def pilot(p, check_eliminated=False, verify_screen=None):
    start = perf_counter()
    d = p - 1
    assert p > 9 and s.ZZ(p).is_prime()
    assert pow(3, d, p * p) == 1 and pow(2, d, p * p) != 1
    l2 = (-(pow(2, d, p * p) - 1) // p) % p
    l3 = (-(pow(3, d, p**3) - 1) // (p * p)) % p
    w = int(s.GF(p).multiplicative_generator())
    zs = [1]
    for _ in range(1, d):
        zs.append(zs[-1] * w % p)
    ring = s.PolynomialRing(s.Integers(p), "x")
    chirp = [zs[(-i * (i - 1) // 2) % d] for i in range(d)]
    kernel = ring([zs[(i * (i - 1) // 2) % d] for i in range(2 * d - 1)])
    inv = [0, 1]
    for i in range(2, p):
        inv.append(-(p // i) * inv[p % i] % p)
    coeff = inv[-1:] + inv[1:-1]
    base = coeff
    rows = []
    for m in range(1, 5):
        f = ring([x * y % p for x, y in zip(coeff, chirp)][::-1])
        conv = f * kernel
        # c_m(a) = Li_m(zeta_a)/p^m mod p = sum a^i/i^m / (a-1).
        row = [0] * p
        for j in range(1, d):
            a = zs[j]
            row[a] = int(conv[d - 1 + j]) * chirp[j] * inv[a - 1] % p
        rows.append(row)
        coeff = [x * y % p for x, y in zip(coeff, base)]
    table_time = perf_counter() - start
    c1, c2, c3, c4 = rows
    r = []
    for a, l in ((3, l3), (9, 2 * l3 % p)):
        r.append((c4[a], l * c3[a] % p, pow(l, 3, p) * c1[a] % p))
    a, b = r
    A, B, C = [
        (a[(i + 1) % 3] * b[(i + 2) % 3] - a[(i + 2) % 3] * b[(i + 1) % 3]) % p for i in range(3)
    ]
    assert l2 and l3 and c2[3] and A and B and C
    scale = -l2 * l3 * inv[c2[3]] % p
    surviving_zero = []
    surviving_other = []
    singular = []
    unresolved = []
    for a in range(2, p):
        # Write L=log(x)/p, Y_m=Li_m(x)/p^m, h=a/(1-a). In the
        # residue field Y_1=c1+h*L and Y_2=c2+c1*L+h*L^2/2.
        # The first equations reduce to c2[3]*L*Y_1 and C*L^3*Y_1.
        # Thus L or Y_1 vanishes. If c1=0, both vanish and f2/p^5
        # reduces to l2*l3*c2. Retain ambiguous singular discs.
        if c1[a] == 0:
            singular.append(a)
            if c2[a] == 0:
                unresolved.append(a)
            continue
        # For L=p*u, f2/p^5 determines u, then f4/p^16 tests it.
        u = scale * c2[a] * inv[c1[a]] % p
        if (A * c4[a] + B * u * c3[a] + C * pow(u, 3, p) * c1[a]) % p == 0:
            surviving_zero.append(a)
        # For L nonzero and Y_1=p*v, f4/p^14 forces v=0 mod p.
        # Then f2/p^5 forces Y_2=0, or 2*c2-c1^2/h=0.
        if (2 * c2[a] * a - c1[a] ** 2 * (1 - a)) % p == 0:
            surviving_other.append(a)
    print(
        "p",
        p,
        "tables seconds",
        round(table_time, 3),
        "complete pilot",
        round(perf_counter() - start, 3),
        "leading minor units",
        A,
        B,
        C,
    )
    print("singular discs", len(singular), singular[:50], "unresolved singular", unresolved[:50])
    print("survivors log-zero branch", len(surviving_zero), surviving_zero[:50])
    print("survivors Li1-zero branch", len(surviving_other), surviving_other[:50])
    assert {v % p for v in (-3, -1, 3, 9)} <= set(surviving_zero + unresolved)
    one_one = [a for a in range(2, p) if c2[a] == 0 and c4[a] == 0]
    discs = set(surviving_zero + surviving_other + unresolved)
    selected = discs | set(one_one) | {2, 3, 9}
    leading = {a: [row[a] for row in rows] for a in selected}
    if check_eliminated:
        eliminated = [a for a in range(2, p) if a not in selected]
        sample = Random(p).sample(eliminated, min(20, len(eliminated)))
        # Limit how many million-entry lists the direct sums hold at once.
        for i in range(0, len(sample), 4):
            direct = sparse_tables(p, 1, sample[i : i + 4])
            for a, values in direct.items():
                assert [(-v) % p for v in values] == [row[a] for row in rows], a
        print("All four Fourier entries matched direct sums on eliminated discs", sample)
    if verify_screen:
        check_field_table(
            verify_screen,
            p,
            rows,
            {
                "one-one": one_one,
                "singular": singular,
                "unresolved": unresolved,
                "log-zero": surviving_zero,
                "li1-zero": surviving_other,
            },
        )
    return discs, one_one, leading, (l2, l3, c2[3], A, B, C)


def sparse_tables(p, r, residues):
    """Evaluate the first r moment terms at selected Teichmuller points."""
    mod = p**r
    inv = [pow(a, -1, mod) for a in range(1, p)]
    zetas = {a: pow(a, mod, mod) for a in residues}
    weights = {}
    for a, z in zetas.items():
        zs = [z]
        for _ in range(2, p):
            zs.append(zs[-1] * z % mod)
        weights[a] = zs
    spectra = {a: [] for a in residues}
    powers = inv
    for j in range(r + 3):
        for a in residues:
            spectra[a].append(sum(u * v for u, v in zip(weights[a], powers)) % mod)
        if j < r + 2:
            powers = [u * v % mod for u, v in zip(powers, inv)]
    rows = {}
    for a, z in zetas.items():
        d = pow(1 - z, -1, mod)
        moments = [d]
        for j in range(1, r):
            moments.append(z * d * sum(comb(j, i) * moments[i] for i in range(j)) % mod)
        rows[a] = [
            sum(
                (-p) ** j * comb(m + j - 1, j) * moments[j] * spectra[a][m + j - 1]
                for j in range(r)
            )
            % mod
            for m in range(1, 5)
        ]
    return rows


def lincomb(terms):
    out = [0] * max(len(poly) for _, poly in terms)
    for c, poly in terms:
        for i, v in enumerate(poly):
            out[i] += c * v
    return out


def mul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return out


def evaluate(f, t):
    out = 0
    for a in reversed(f):
        out = out * t + a
    return out


def local_tables(p, r, n, rows):
    """On zeta+p*t use (zeta+p*t) Li_m' = p Li_(m-1)."""
    K = s.Qp(p, n + 8)
    pp = s.ZZ(p)
    discs = {}
    for a, vs in rows.items():
        z = K.teichmuller(a)
        li = [[z / (1 - z)] + [pp**k / (1 - z) ** (k + 1) for k in range(1, n)]]
        log = [K(0)] + [-((-pp / z) ** k) / k for k in range(1, n)]
        for m, v in enumerate(vs, 1):
            coeff = [K(v).add_bigoh(r) * pp**m / (pp**m - 1)]
            for k in range(1, n):
                coeff.append(pp * (li[-1][k - 1] - (k - 1) * coeff[-1]) / (k * z))
            li.append(coeff)
        discs[a] = z, log, li
    return discs


def mod_eval(f, t, modulus):
    value = 0
    for c in reversed(f):
        value = (value * t + c) % modulus
    return value


def normalized(f, p, n):
    modulus = p**n
    for loss in range(n):
        if any(c % p for c in f):
            # Coefficients, including the unrepresented tail, have absolute
            # error in p^n Z_p. Division leaves error in p^(n-loss) Z_p.
            # Termwise differentiation in the integral t-coordinate
            # multiplies by integer indices and preserves this error ideal.
            assert n >= loss + 1 and modulus == p ** (n - loss)
            return f, modulus, loss
        f = [c // p for c in f]
        modulus //= p
    raise ArithmeticError("precision exhausted before finding a unit coefficient")


def finite(poly, p, n):
    digits = min(
        [n] + [int(c.precision_absolute()) for c in poly if c.precision_absolute() != s.Infinity]
    )
    assert digits > 0
    return normalized([int(c.lift()) % p**digits for c in poly], p, digits)


def finish(p, r, discs, one_one, leading, screen_units):
    start = perf_counter()
    n = max(24, 15 + r)
    if n > p - 4:
        raise ValueError("Requested precision exceeds the proven large-prime Taylor bound.")
    rows = sparse_tables(p, r, sorted(leading))
    # The direct sums use no Fourier transform. At a Teichmuller point,
    # Li_m/p^m = D_m/(p^m-1), so the leading digit is -D_m modulo p.
    assert all([(-v) % p for v in row] == leading[a] for a, row in rows.items())
    print("sparse tables seconds", round(perf_counter() - start, 3), flush=True)
    print("Taylor cutoff", n, "depleted digits", r)
    # Taylor coefficient k has valuation >= k - 4*floor(log_p(k)).
    # For n <= p-4 all terms k >= n therefore vanish modulo p^n.
    data = local_tables(p, r, n, rows)

    def at(a):
        z, log, li = data[a]
        t = (a - z) / p
        return [evaluate(f, t).add_bigoh(n) for f in (log, *li[1:])]

    l2 = at(2)[0]
    l3, l13, l23, l33, l43 = at(3)
    l9, l19, _, l39, l49 = at(9)
    a = [l43, l3 * l33, l3**3 * l13]
    b = [l49, l9 * l39, l9**3 * l19]
    minors = [a[(i + 1) % 3] * b[(i + 2) % 3] - a[(i + 2) % 3] * b[(i + 1) % 3] for i in range(3)]
    valuations = (12, 11, 9)
    assert [int(v.valuation()) for v in minors] == list(valuations)
    scales = (1, 2, 2, *valuations)
    units = [c / p**v for c, v in zip((l2, l3, l23, *minors), scales)]
    assert all(c.precision_absolute() >= 1 for c in units)
    assert tuple(int(c.residue()) for c in units) == screen_units
    print("Scaled log2, log3, Li2(3) and cofactor residues:", screen_units)
    poly = s.PolynomialRing(s.GF(p), "t")
    known = (-3, -1, 3, 9)
    roots = []
    excluded = []
    records = []
    for disc in sorted(discs):
        z, log, li = data[disc]
        f, q2, v2 = finite(lincomb([(l2 * l3, li[2]), (l23, mul(log, li[1]))]), p, n)
        g, q4, v4 = finite(
            lincomb(
                list(zip(minors, [li[4], mul(log, li[3]), mul(mul(mul(log, log), log), li[1])]))
            ),
            p,
            n,
        )
        assert (v2, v4) == (4, 13)
        for t in sorted(poly(f).roots(multiplicities=False), key=int):
            t = int(t)
            deriv = mod_eval([i * x for i, x in enumerate(f) if i], t, p)
            assert deriv != 0
            record = {"disc": disc, "t0": t, "simple": True, "F2prime_res": deriv}
            records.append(record)
            points = [a for a in known if (a - int(z.lift()) - p * t) % (p * p) == 0]
            if points:
                assert len(points) == 1
                u = (points[0] - int(z.lift())) // p
                assert mod_eval(f, u, q2) == 0 and mod_eval(g, u, q4) == 0
                record.update(status="integral_point", point=str(points[0]), vF4=None)
                roots += points
                continue
            step = p
            value = mod_eval(g, t, step)
            while value == 0 and step < min(q2, q4):
                res = mod_eval(f, t, step * p)
                assert res % step == 0
                t += step * ((-(res // step) * pow(deriv, -1, p)) % p)
                step *= p
                value = mod_eval(g, t, step)
            if value == 0:
                raise ArithmeticError(f"Unresolved root at disc {disc}")
            valuation = int(s.ZZ(step).valuation(p)) - 1
            record.update(
                status="excluded",
                vF4=valuation,
                F4_digit=value // (step // p),
                excluded_mod=f"p^{valuation + 1}",
            )
            excluded.append((disc, valuation + 1))
    other = [a for a in one_one if rows[a][1] == 0 and rows[a][3] == 0]
    assert sorted(roots) == sorted(known) and other == [p - 1]
    print("integral matches", sorted(roots), "excluded (disc, normalised digits)", excluded)
    print(
        "(1,1) from",
        one_one,
        "to",
        other,
        "total follow-up seconds",
        round(perf_counter() - start, 3),
        flush=True,
    )

    return records


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-screen", type=Path, metavar="EXECUTABLE")
    parser.add_argument("--lifts", type=Path, metavar="JSONL", help="write all simple root classes")
    parser.add_argument("--digits", type=int, default=6)
    parser.add_argument(
        "--check-eliminated",
        action="store_true",
        help="compare four weights on 20 reproducibly sampled eliminated discs",
    )
    args = parser.parse_args()
    if not __debug__ or args.digits < 2:
        raise ValueError("Checks require assertions enabled and at least two digits.")
    start = perf_counter()
    p = 1006003
    candidates, one_one, leading, units = pilot(p, args.check_eliminated, args.verify_screen)
    records = finish(p, args.digits, candidates, one_one, leading, units)
    if args.lifts:
        args.lifts.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in records))
    print("whole pilot seconds", round(perf_counter() - start, 3))

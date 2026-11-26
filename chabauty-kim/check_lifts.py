"""
Independent reproduction of refined Chabauty-Kim exclusions for S = {2,3}, depth 4 (Ludtke 2024, Thms 3.4/3.8).

  f2(z) = log2 * log3 * Li2(z) + Li2(3) * log(z) * Li1(z)                    (a_{tau3 tau2} = -Li2(3))
  f4(z) = det [[Li4(z), log z Li3(z), log(z)^3 Li1(z)],
               [Li4(3), log 3 Li3(3), log(3)^3 Li1(3)],
               [Li4(9), log 9 Li3(9), log(9)^3 Li1(9)]]

p-adic functions are Coleman functions with log p = 0.  On the residue disc of a (a != 0, 1) with Teichmuller
centre zeta, Li_n(zeta) = p^n/(p^n - 1) * Li^(p)_n(zeta), where the depleted value is the Abel-regularised sum
   Li^(p)_n(zeta) = sum_{p not| m} zeta^m m^-n = sum_{j>=0} C(n-1+j, j) (-p)^j mu_j(zeta) S_{n+j}(zeta),
   S_k(zeta) = sum_{a=1}^{p-1} a^-k zeta^a,   mu_0 = 1/(1-zeta),   mu_j (1-zeta) = zeta sum_{i<j} C(j,i) mu_i,
(write m = a + p b, zeta^p = zeta, expand (a + p b)^-n binomially, mu_j = Abel sum of b^j zeta^b).
Local series in t = (z - zeta)/p come from d Li_n = Li_{n-1} dz / z and Li1 = -log(1 - z).
All arithmetic is exact modulo P = p^K (absolute precision K).
"""

import sys
import time
from contextlib import redirect_stdout
from math import comb

import numpy as np
from gmpy2 import invert, mpz, powmod

p = int(sys.argv[1]) if len(sys.argv) > 1 else 1006003
K = int(sys.argv[2]) if len(sys.argv) > 2 else 26  # absolute p-adic digits
if not __debug__ or p != 1006003 or not (20 <= K <= p - 6):
    raise ValueError("Use assertions and 20 <= K <= p-6 for the p=1006003 certificate.")
T = K + 2  # t-degree cutoff (tail valuation >= k - 4 floor(log_p k))
P = mpz(p) ** K
NMAX = 4
TABLE_DISCS = (
    [int(x) for x in sys.argv[3].split(",")]
    if len(sys.argv) > 3
    else [2, 3, 9, 335334, 670669, 894225, 1006000, 1006002]
)


def teich(a):
    return powmod(mpz(a) % p, mpz(p) ** (K - 1), P)


def log_unit(u):
    """Coleman/Iwasawa log (log p = 0) of a p-adic unit u (mod P)."""
    u = mpz(u) % P
    x = (u * invert(teich(int(u % p)), P) - 1) % P  # v(x) >= 1
    s = mpz(0)
    xk = mpz(1)
    for k in range(1, K + 3):
        xk = xk * x % P
        term = xk * invert(k, P) % P
        s = (s + term) % P if k % 2 else (s - term) % P
    return s


# ---------------- series helpers (lists of mpz mod P, length T) ----------------
def smul(A, B):
    C = [mpz(0)] * T
    for i, a in enumerate(A):
        if a:
            for j in range(T - i):
                if B[j]:
                    C[i + j] = (C[i + j] + a * B[j]) % P
    return C


def sadd(A, B):
    return [(a + b) % P for a, b in zip(A, B)]


def sscale(A, c):
    return [a * c % P for a in A]


def disc_series(a, Lz):
    """Series in t (z = zeta + p t) for log z, Li1..Li4 on the disc of a, given Teichmuller values Lz[n]."""
    z0 = teich(a)
    iz = invert(z0, P)
    pz = mpz(p)
    # log(zeta + p t) = log(1 + p t / zeta)
    logs = [mpz(0)] * T
    for k in range(1, T):
        c = powmod(pz * iz % P, k, P) * invert(k, P) % P
        logs[k] = c if k % 2 else (-c) % P
    # Li1 = -log(1 - zeta - p t) = -log(1-zeta) - log(1 - p t/(1-zeta)) = -log(1-zeta) + sum (p t/(1-zeta))^k / k
    w = invert((1 - z0) % P, P)
    li = {
        1: [(-log_unit((1 - z0) % P)) % P]
        + [powmod(pz * w % P, k, P) * invert(k, P) % P for k in range(1, T)]
    }
    # 1/(zeta + p s) = zeta^-1 sum (-p s / zeta)^m
    inv_z = [(iz * powmod((-pz * iz) % P, m, P)) % P for m in range(T)]
    for n in range(2, NMAX + 1):
        integrand = sscale(smul(li[n - 1], inv_z), pz)  # p * Li_{n-1}(zeta + p s) / (zeta + p s)
        s = [mpz(0)] * T
        s[0] = Lz[n] % P
        for k in range(T - 1):
            s[k + 1] = integrand[k] * invert(k + 1, P) % P
        li[n] = s
    return logs, li


def teich_polylogs(discs):
    """Li_n(zeta_a) for n = 1..4 and each disc a, via one pass over a' = 1..p-1."""
    J = K  # j < K suffices: (-p)^j
    kmax = NMAX + J
    zs = {a: teich(a) for a in discs}
    S = {a: [mpz(0)] * (kmax + 1) for a in discs}
    zpow = {a: mpz(1) for a in discs}
    t0 = time.time()
    for b in range(1, p):
        ib = invert(mpz(b), P)
        powk = [mpz(1)] * (kmax + 1)
        for k in range(1, kmax + 1):
            powk[k] = powk[k - 1] * ib % P
        for a in discs:
            zpow[a] = zpow[a] * zs[a] % P
            zb = zpow[a]
            Sa = S[a]
            for k in range(1, kmax + 1):
                Sa[k] += powk[k] * zb
        if b % 100000 == 0:
            for a in discs:
                S[a] = [x % P for x in S[a]]
            print(f"  sums: {b}/{p}  {time.time() - t0:.0f}s", file=sys.stderr, flush=True)
    out = {}
    for a in discs:
        z = zs[a]
        Sa = [x % P for x in S[a]]
        omz = invert((1 - z) % P, P)
        mu = [omz]
        for j in range(1, J):
            acc = sum(comb(j, i) * mu[i] for i in range(j)) % P
            mu.append(z * omz % P * acc % P)
        L = {}
        for n in range(1, NMAX + 1):
            dep = mpz(0)
            for j in range(J):
                dep += comb(n - 1 + j, j) * powmod(mpz(-p) % P, j, P) % P * mu[j] % P * Sa[n + j]
            dep %= P
            pn = mpz(p) ** n
            L[n] = pn * dep % P * invert((pn - 1) % P, P) % P
        out[a] = L
    return out


def val(x):
    x = mpz(x) % P
    if x == 0:
        return K
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def series_eval(A, t):
    r = mpz(0)
    for c in reversed(A):
        r = (r * t + c) % P
    return r


def main(output):
    a2, a3 = 25314, 3
    discs = sorted({a2, a3, 9, p - 3, p - 1} | set(TABLE_DISCS))
    print(f"p={p} K={K} T={T} discs={discs}", file=sys.stderr)
    TL = teich_polylogs(discs)
    D = {a: disc_series(a, TL[a]) for a in discs}

    def at_point(z):  # values of log, Li1..4 at an integer point z
        a = z % p
        t = (mpz(z) - teich(a)) % P
        assert t % p == 0
        t //= p
        logs, li = D[a]
        return series_eval(logs, t), {n: series_eval(li[n], t) for n in li}

    log2 = log_unit(2)
    log3 = log_unit(3)
    log9 = log_unit(9)
    lg3, L3 = at_point(3)
    lg9, L9 = at_point(9)
    assert (val(log2), val(log3)) == (1, 2)
    assert lg3 == log3 and lg9 == log9 and (L3[1] + log2) % P == 0
    print("checks:")
    print("  v(log2), v(log3) =", val(log2), val(log3))
    print("  log at 3 == log_unit(3):", lg3 == log3, "; Li1(3) == -log2:", (L3[1] + log2) % P == 0)
    for a in discs:  # Li1 Teichmuller value vs direct -log(1-zeta)
        z = teich(a)
        assert (TL[a][1] + log_unit((1 - z) % P)) % P == 0, a
    print("  Li1(zeta_a) == -log(1 - zeta_a) on all discs: True")
    Li2_3 = L3[2]

    def f2(lg, L):
        return (log2 * log3 % P * L[2] + Li2_3 * lg % P * L[1]) % P

    row3 = (L3[4], lg3 * L3[3] % P, powmod(lg3, 3, P) * L3[1] % P)
    row9 = (L9[4], lg9 * L9[3] % P, powmod(lg9, 3, P) * L9[1] % P)

    def det3(r1, r2, r3):
        (a, b, c), (d, e, f), (g, h, i) = r1, r2, r3
        return (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % P

    def f4(lg, L):
        return det3((L[4], lg * L[3] % P, powmod(lg, 3, P) * L[1] % P), row3, row9)

    for z in (-3, -1, 3, 9):
        lg, L = at_point(z)
        assert f2(lg, L) == f4(lg, L) == 0
        print(f"  f2({z}) valuation = {val(f2(lg, L))} (K={K} means 0)", end="")
        print(f",  f4({z}) valuation = {val(f4(lg, L))}")
    _, Lm3 = at_point(-3)
    assert (Lm3[2] - 2 * Li2_3) % P == (L9[2] - 6 * Li2_3) % P == 0
    print(
        "  identities: Li2(-3) == 2 Li2(3):",
        (Lm3[2] - 2 * Li2_3) % P == 0,
        "; Li2(9) == 6 Li2(3):",
        (L9[2] - 6 * Li2_3) % P == 0,
    )

    # ---------------- power series of f2, f4 on a disc ----------------
    def F_series(a):
        logs, li = D[a]
        f2s = sadd(sscale(li[2], log2 * log3 % P), sscale(smul(logs, li[1]), Li2_3))
        lg3s = smul(smul(logs, logs), logs)
        c1 = (row3[1] * row9[2] - row3[2] * row9[1]) % P
        c2 = (row3[0] * row9[2] - row3[2] * row9[0]) % P
        c3 = (row3[0] * row9[1] - row3[1] * row9[0]) % P
        f4s = sadd(
            sadd(sscale(li[4], c1), sscale(smul(logs, li[3]), (-c2) % P)),
            sscale(smul(lg3s, li[1]), c3),
        )
        return f2s, f4s

    print("\ncontrols:")
    L = TL[a2]
    print(
        f"  disc {a2}: c1 = p^-1 Li1(zeta) mod p = {(L[1] // p) % p}  (v={val(L[1])}),"
        f"  c2 = p^-2 Li2(zeta) mod p = {(L[2] // p**2) % p}  (v={val(L[2])})"
    )
    f2s, _ = F_series(a3)
    print(f"  disc {a3}: min v(f2 coeffs) = {min(val(c) for c in f2s)}")
    t3 = ((mpz(3) - teich(3)) % P) // p
    dF2 = [(k * f2s[k]) % P for k in range(1, T)]
    d = series_eval(dF2, t3)
    print(f"  disc {a3}: F2'(t) at z=3: v(f2')={val(d)}, (f2'/p^4) mod p = {(d // p**4) % p}")

    # ---------------- table over the requested discs ----------------
    rows = []
    for a in TABLE_DISCS:
        f2s, f4s = F_series(a)
        v2 = min(val(c) for c in f2s)
        v4 = min(val(c) for c in f4s)
        assert v2 == 4 and v4 == 13, (a, v2, v4)
        Pp = mpz(p) ** (K - 4)
        F2 = [(c // p**4) % Pp for c in f2s]
        coeff = np.array([int(c % p) for c in F2], dtype=np.int64)
        ts = np.arange(p, dtype=np.int64)
        acc = np.zeros(p, dtype=np.int64)
        for c in coeff[::-1]:
            acc = (acc * ts + c) % p
        roots = [int(x) for x in np.nonzero(acc == 0)[0]]
        dF2 = [(k * F2[k]) % Pp for k in range(1, len(F2))]
        z0 = teich(a)
        for r in roots:
            t = mpz(r)
            der = series_eval(dF2, t) % Pp
            if der % p == 0:
                raise ArithmeticError(f"Non-simple F2 root at {(a, r)}")
            for _ in range((K - 4).bit_length()):
                t = (t - series_eval(F2, t) * invert(der, Pp)) % Pp
                der = series_eval(dF2, t) % Pp
            zl = (z0 + p * t) % P
            assert series_eval(F2, t) % Pp == 0
            f4v = series_eval(f4s, t)
            v = val(f4v)
            row = {"disc": a, "t0": r, "simple": True, "F2prime_res": int(der % p)}
            if v < K:
                row.update(
                    status="excluded",
                    vF4=v - 13,
                    F4_digit=int((f4v // mpz(p) ** v) % p),
                    excluded_mod=f"p^{v - 12}",
                )
            else:
                matches = [z for z in (-3, -1, 3, 9) if (z - zl) % (p * Pp) == 0]
                if len(matches) != 1:
                    raise ArithmeticError(f"Unresolved common root at {(a, r)}")
                row.update(status="integral_point", point=str(matches[0]), vF4=None)
            rows.append(row)
        assert len(roots) == 2, (a, roots)
    import json

    for r in rows:
        print(json.dumps(r, sort_keys=True), file=output)


if __name__ == "__main__":
    output = sys.stdout
    with redirect_stdout(sys.stderr):
        main(output)

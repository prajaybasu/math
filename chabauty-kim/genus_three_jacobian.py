"""Certify the reduction image of the rank-one logarithmic Chabauty locus.

Run with sage -python jacobian_screen.py [prime ...]. CHART_SEED selects the
random sequence of auxiliary divisors. All congruences are exact. Coordinates
refer to the original degree-seven model, with rational basepoint infinity.
"""
import csv
import os
import random
import sys

from sage.all import GF, PolynomialRing, Zmod, matrix, pari, prime_range, vector


class SingularChart(Exception):
    """A denominator or leading interpolation coefficient vanishes mod p."""


def run(p):
    F = GF(p)
    R = PolynomialRing(F, 'x')
    K = Zmod(p**4)
    L = Zmod(p**3)
    S = PolynomialRing(K, 'x')
    x = S.gen()
    f = S([8, 32, 32, -16, -36, -8, 9, 4])
    # At x=0 the two conjugate factors have product x^12, proving
    # 12[(0,2 sqrt(2))-infinity]=0. At x=±1 both signs are rational.
    A = -x**6-16*x**5-36*x**4+72*x**2+64*x+16
    B = x**2+4*x+2
    assert A**2-8*f*B**2 == x**12
    assert f(1) == K(25) and f(-1) == K(1)
    ff = R(f)
    assert p > 2 and ff.is_squarefree()
    n = int(pari(ff).hyperellcharpoly().subst('x', 1))

    points = {}
    for a in range(p):
        q = ff(F(a))
        if q and q.is_square():
            y = int(q.sqrt())
            for place in (p, p**2, p**3):
                dy = (int(f(a)) - y*y) // place
                y += place * (dy * pow(2*y, -1, p) % p)
            assert K(y*y) == f(a)
            points[a] = y

    branch = 1 + len(ff.roots())
    total = branch + 2*len(points)
    witnesses = set(points).intersection({0, 1, p-1})
    exact = branch + 2*len(witnesses)
    if total == exact:
        return p, n, total, exact, exact, exact, exact, ' '.join(map(str, sorted(witnesses)))

    def inv(a, modulus):
        h, b, _ = R(a).xgcd(R(modulus))
        if h != 1:
            raise SingularChart
        b = S(b)
        for _ in range(2):
            b = (b*(2-a*b)) % modulus
        return b

    def add(A, B, doubling=False):
        u, v = A
        w, z = B
        if doubling:
            c = (((f-v*v)//u) * inv(2*v, u)) % u
        else:
            c = ((z-v)*inv(u, w)) % w
        v += c*u
        u *= w
        while u.degree() > 3:
            # A nonunit top coefficient can hide a pole at infinity mod p^k.
            if v.degree() > 3 and int(v.leading_coefficient()) % p == 0:
                raise SingularChart
            u = (f-v*v)//u
            if int(u.leading_coefficient()) % p == 0:
                raise SingularChart
            u = u.monic()
            v = (-v) % u
        return u, v % u

    E = GF(p**3, 'b')
    basis = [E.gen()**i for i in range(3)]

    def random_divisor(rng):
        while True:
            b = sum(rng.randrange(p)*z for z in basis)
            u = R(b.minpoly())
            if u.degree() != 3:
                continue
            q = ff(b)
            if not q or not q.is_square():
                continue
            c = q.sqrt()
            M = matrix(F, [[(b**i).polynomial()[j] for j in range(3)] for i in range(3)])
            coords = vector(F, [c.polynomial()[j] for j in range(3)])
            v = S(list(M.solve_left(coords)))
            u = S(u)
            for _ in range(2):
                v = (v + (f-v*v)*inv(2*v, u)) % u
            assert (f-v*v) % u == 0
            return u, v

    def jets(i, xx, iy, df, ddf):
        # Coefficient of x^i dx/(2y) and its first two x-derivatives.
        a = xx**i
        da = i*xx**(i-1) if i else 0
        dda = 2 if i == 2 else 0
        return (a*iy, da*iy - 2*a*df*iy**3,
                dda*iy - 4*da*df*iy**3 - 2*a*ddf*iy**3 + 12*a*df**2*iy**5)

    def liftlog(a, y):
        """Compute log(n[(a,y)-infinity])/p in (Z/p^3)^3."""
        P = (x-a, S(y))
        rng = random.Random(int(os.getenv('CHART_SEED', '315')) + a % p)
        for _ in range(1500):
            try:
                T = random_divisor(rng)
                u, v = T
                neg = (u, -v)
                C = add(P, neg)
                A = add(P, T)
                # Binary ladder with accumulator A = kP + T.
                for bit in bin(n)[3:]:
                    A = add(add(A, A, True), C if bit == '1' else neg)
                assert R(A[0]) == R(u) and R(A[1]) == R(v)
                au = A[0]
                # In K[x]/u the nearby point has x-coordinate x+delta.
                delta = (-au*inv(au.derivative(), u)) % u
                residual = (au + au.derivative()*delta + au.derivative(2)*delta**2/K(2)
                            + au.derivative(3)*delta**3/K(6))
                delta = (delta - residual*inv(au.derivative() + au.derivative(2)*delta, u)) % u
                assert au(x+delta) % u == 0
                iy = inv(2*v, u)
                values = []
                for i in range(3):
                    d, e, g = jets(i, x, iy, f.derivative(), f.derivative(2))
                    integ = (d*delta + e*delta**2/K(2) + g*delta**3/K(6)) % u
                    trace = 3*integ[0] - u[2]*integ[1] + (u[2]**2-2*u[1])*integ[2]
                    assert int(trace) % p == 0
                    values.append(L(int(trace)//p))
                return vector(L, values)
            except SingularChart:
                continue
        raise ArithmeticError(f'No regular chart for p={p}, x={a}')

    # p=3,7 are saturated by witnesses before divisions by 6 or chart selection.
    assert p >= 5
    a = p-1
    y = points[a]
    iy = 1/L(2*y)
    at_a = [jets(i, L(a), iy, L(f.derivative()(a)), L(f.derivative(2)(a))) for i in range(3)]
    # Translate x=p-1 to x=-1 on the same sheet. Either sign spans the same line.
    D = liftlog(a, y) + vector(L, [n*(-d+p*e/2-p**2*g/6) for d, e, g in at_a])
    pivot = next(i for i in range(3) if int(D[i]) % p)

    def ann(v):
        return [v[i]-v[pivot]*D[i]/D[pivot] for i in range(3) if i != pivot]

    survivors = [set(witnesses) for _ in range(3)]
    for a, y in points.items():
        if a in witnesses:
            continue
        w = ann(liftlog(a, y))
        iy = 1/L(2*y)
        at_a = [jets(i, L(a), iy, L(f.derivative()(a)), L(f.derivative(2)(a))) for i in range(3)]
        t, c, h = [ann(n*vector(L, z)) for z in zip(*at_a)]
        equations = list(zip(w, t, c, h))
        roots = [0]
        for level in range(1, 4):
            modulus = p**level
            place = p**(level-1)
            candidates = (b+k*place for b in roots for k in range(p))
            roots = [z for z in candidates if all(
                int(v+z*d+p*z**2*e/2+p**2*z**3*g/6) % modulus == 0
                for v, d, e, g in equations)]
            if not roots:
                break
            survivors[level-1].add(a)
    assert survivors[-1] == witnesses
    counts = [branch+2*len(group) for group in survivors]
    return p, n, total, *counts, exact, ' '.join(map(str, sorted(witnesses)))


if __name__ == '__main__':
    primes = map(int, sys.argv[1:]) if sys.argv[1:] else prime_range(3, 200)
    writer = csv.writer(sys.stdout, lineterminator='\n')
    writer.writerow(('p', 'jacobian_order', 'all_discs', 'scaled_digit_1', 'scaled_digit_2',
                     'scaled_digit_3', 'occupied', 'nonbranch_witness_x'))
    for prime in primes:
        writer.writerow(run(int(prime)))
        sys.stdout.flush()

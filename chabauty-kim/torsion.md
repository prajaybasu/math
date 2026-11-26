# Fixed depth on the torsion component

For the thrice-punctured line over the rationals with $S=\{2,3\}$, the target is equality of the full refined depth-four locus with the 21 integral points for a set of auxiliary primes of Dirichlet density one. Lüdtke's Lemma 3.1 gives a sufficient reduction to the two components $(1,1)$ and $(1,0)$. On $(1,1)$ the equations include $\log(z)=\operatorname{Li}_2(z)=\operatorname{Li}_4(z)=0$. Every such point is a Teichmüller root of unity reducing to $a\in\mathbb F_p\setminus\{0,1\}$. The integral point $-1$ belongs to this component. These facts hold for $S=\{2,q\}$ with any odd prime $q\ne p$. [Lüdtke, Lemma 3.1, Theorem 3.2 and Remark 3.3](https://arxiv.org/html/2402.03573v2#S3)

The fixed depth matters. At weight $p-3$, Betts–Kumpitsch–Lüdtke already isolate $-1$ for every $p\ge5$. They also cite Stix for the $S$-Selmer Section Conjecture on this rational curve for every $S$. A density-one determination at depth four would give another route to that consequence. [Betts–Kumpitsch–Lüdtke, introduction and Proposition 5.15](https://arxiv.org/html/2305.09462) · [Stix, Corollary 6](https://arxiv.org/abs/1203.3236)

## A sufficient cross-prime criterion

Write $\ell_m(X)=\sum_{j=1}^{p-1}j^{-m}X^j$. For $p\ge7$, Besser's reduction implies that any common Coleman zero above has $\ell_2(a)=\ell_4(a)=0$. Here the factor $a-1$ in the normalization is a unit. The implication from an exact zero to a finite-field zero goes in this direction. [Besser, Proposition 2.1](https://arxiv.org/pdf/math/0006051)

Let $B_0=1$ and $B_{n+1}=X((1-X)B_n'+(n+1)B_n)$. For $n>0$, $B_n$ is $X$ times the ordinary Eulerian polynomial. For $n+m=p-1$, $n>0$, one has the polynomial identity
$$
(1-X)^{n+1}\ell_m(X)=(1-X^p)B_n(X)\quad\text{in }\mathbb F_p[X].
$$
Indeed the Euler derivative $X\,d/dX$ multiplies the coefficient of $X^j$ by $j$. Its $n$th iterate on $1+X+\cdots+X^{p-1}$ yields $\ell_m$ by Fermat's theorem. Differentiating the cleared geometric identity gives the stated recurrence because $(X^p)'=0$. For $a\in\mathbb F_p$ with $a\ne1$, both prefactors in the identity are units on evaluation. [Lean proof](../lean/BBPGrouping/TorsionDisc.lean)

Put
$$
M_p=\frac{X^{p-1}-1}{X^2-1},\qquad
G_p=\gcd(M_p,B_{p-3},B_{p-5})
$$
with monic gcd over $\mathbb F_p$. The first polynomial is the product of the distinct linear factors for all $a\notin\{0,1,-1\}$. Thus $\deg G_p$ counts exactly the extra common zeros of the **two reductions**. If $G_p=1$, the only possible residue for the $(1,1)$ component is $-1$, with unique Teichmüller lift $-1$. Lean proves this last implication given the two finite-polylogarithm vanishings. If $G_p$ has positive degree, its roots are the residues requiring higher precision.

A sufficient target for this component is that the primes with $\deg G_p>0$ have Dirichlet density zero. For example, the stronger first-moment estimate
$$
\sum_{7\le p\le x}\deg G_p=o(\pi(x))
$$
would suffice, since each exceptional prime contributes at least one. The existing per-prime power saving bounds the size of a possible exception, and supplies no estimate of this average tending to zero. The distribution of these split common factors across primes and the separate $(1,0)$ component remain open in this argument.

## Reproducible finite check

In Sage the equivalent finite-polylogarithm gcd avoids constructing large integer Eulerian coefficients. This checks all 427 primes from 7 through 3000 and finds $G_p=1$ at each. This lies inside Lüdtke's published range.

```python
from sage.all import GF, PolynomialRing, prime_range

checked = 0
for prime in prime_range(7, 3001):
    p = int(prime)
    R = PolynomialRing(GF(p), "x")
    x = R.gen()
    inv = [0, 1]
    for j in range(2, p):
        inv.append(-(p // j) * inv[p % j] % p)
    l2 = R([a**2 % p for a in inv])
    l4 = R([a**4 % p for a in inv])
    M = (x**(p-1) - 1) // (x**2 - 1)
    assert M.gcd(l2).gcd(l4) == 1, p
    checked += 1
assert checked == 427
```

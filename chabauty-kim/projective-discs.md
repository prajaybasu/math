# Occupied residue discs on projective curves

A disc is occupied if it contains a common local zero. On the genus-three example we use the classical abelian Chabauty locus, the inverse image under the Abel–Jacobi logarithm of the rational Mordell–Weil logarithm span. It can contain points defined over extensions of the rationals. Interpreting this span as the image of an étale Selmer group would require the corresponding Selmer comparison.

## Rank one in genus three

Use Example 4.1 of Balakrishnan–Bianchi–Cantoral-Farfán–Çiperiani–Etropolski,
$$
y^2=f(x)=4x^7+9x^6-8x^5-36x^4-16x^3+32x^2+32x+8 .
$$
The rank is one and the divisor $D=(-1,-1)-\infty$ has infinite order. The curve has good reduction at every odd prime below 200. The Jacobian is simple over $\mathbb Q$: its Frobenius polynomial at 3 is $T^6+T^5+2T^4+2T^3+6T^2+9T+27$, irreducible over $\mathbb Q$. A rational isogeny decomposition would factor this polynomial. [Example 4.1 and the published seven-adic calculation](https://arxiv.org/abs/1805.03361)

For a non-Weierstrass affine disc choose a lift $Q_0=(a,y_0)$ and put $x=a+pw$. Project the three integrals of $x^i dx/(2y)$, $0\le i\le2$, onto two coordinates killing $\log D$, using an integral basis of the annihilator. Let $c_i$ be the projected logarithm at $Q_0$ and $u_i$ the projected derivative at its residue. The logarithm changes by $pw u_i\bmod p^2$ because the coefficients of the differential on this chart are integral and $p$ is odd. If either constant is outside $p\mathbb Z_p$, the disc is empty. Otherwise let $a_i=c_i/p\bmod p$. The first digit of $w$ must solve both $a_i+u_i w=0$. For $(u_1,u_2)\ne(0,0)$ this is equivalent to
$$
a_1 u_2-a_2 u_1=0 .
$$
When both slopes vanish, both constants must vanish. Changing the lift translates the constant vector by a multiple of the slope vector. Lean checks compatibility in both cases and invariance of the determinant under translation. The analytic input is local Taylor expansion. [Finite-field lemmas](../lean/BBPGrouping/ProjectiveDisc.lean)

### Reproducing the census

Run the following in this directory with Sage 10.9.

```sh
sage -python genus_three_jacobian.py
sage -python genus_three_discs.py --max-prime 31
```

For every one of the 45 odd primes below 200, the occupied discs consist of the reductions of the local Weierstrass points and the available pairs above $x=-1,1,0$. At $x=0$ the points exist when $8$ is square. Their Abel–Jacobi images are torsion. Indeed, with $A=-x^6-16x^5-36x^4+72x^2+64x+16$ and $B=x^2+4x+2$, one has $A^2-8fB^2=x^{12}$. At $(0,2\sqrt2)$ the factor $A-2\sqrt2\,y B$ vanishes, the conjugate is a unit, and the only pole is at infinity. Thus the divisor of that function is $12P-12\infty$. At $x=\pm1$ the points are rational. A simple branch root lifts to a Weierstrass point. The census counts each residue disc once even when witnesses coincide. [Norm identity in Lean](../lean/BBPGrouping/ProjectiveDisc.lean) · [All counts](genus_three_discs.csv)

The first program computes $n=\#J(\mathbb F_p)$ and $p^{-1}\log([n](Q-\infty))\bmod p^3$. A translated Cantor ladder computes $[n](Q-\infty)+T$ on a regular divisor chart with squarefree support of degree three. Both divisors reduce to $T$. The program Hensel-lifts the nearby support coordinates and traces their tiny integrals. All modular inversions and leading coefficients needed for reductions are units on an accepted chart. For $p\ge5$, terms of order $j\ge4$ in a tiny integral have valuation at least $j-v_p(j)\ge4$. Both $p=3$ and $p=7$ are settled directly by witnesses on every disc. The program tests every allowable lift digit and checks exact witness coverage for the surviving discs. Varying the auxiliary divisors with `CHART_SEED=317` reproduces the default output. When $p\mid n$, an early digit of the scaled log can be uninformative: at $p=41$ the three successive counts are 40, 12 and 10. [Modular Jacobian computation](genus_three_jacobian.py)

The second program computes the ordinary Coleman integrals using Sage, in the monic coordinates $X=4x$, $Y=64y$. Its lower and upper bounds agreed with the modular census at the 27 primes checked separately (all odd primes through 101, plus 137 and 167). It reports separate lower and upper bounds, tests its precision before reduction, and retains ambiguous root classes until the requested depth. At $p=11$ the unscaled first-digit screen leaves 8 of 16 discs and lifting gives 6 occupied. At $p=199$ the modular calculation gives 10 of 184. Finite samples establish these counts and give no asymptotic bound. [Coleman computation](genus_three_discs.py)

### What Cartier controls

Over $\mathbb F_p$, the Cartier–Manin matrix in the holomorphic basis has entries $[x^{pi-j}]f^{(p-1)/2}$ for $1\le i,j\le3$. It has rank three at 43 of these primes and rank two at 5 and 13. The following Sage expression reproduces one matrix for any of the test primes.

```python
F = GF(p)
f = PolynomialRing(F, "x")([8,32,32,-16,-36,-8,9,4])
h = f**((p-1)//2)
M = matrix(F, 3, 3, lambda i, j: h[p*(i+1)-(j+1)])
```

Cartier kills exact differentials. At the ordinary primes an annihilating form with nonzero reduction therefore has no rational primitive on the special fibre. The tangent vector in the disc test is algebraic, while its constants depend on lifted logarithms. In particular one cannot obtain the constants by choosing rational functions whose ordinary derivatives are the annihilating forms. There may be a relation using arithmetic jets or Frobenius correction terms. We have no bound on the degree of such a relation suitable for the several-pole zero estimate. At a good prime with $p\nmid n$, the reduction of $p^{-1}\log([n](Q-\infty))$ changes along the image of the tangent line as the lift varies. Thus its class modulo that line is a first-order object on the arithmetic jet space, and the test projects it further modulo the Mordell–Weil direction. [Achter–Howe on Cartier–Manin matrices](https://arxiv.org/abs/1710.10726) · [Poonen on Greenberg transforms and torsion](https://math.berkeley.edu/~poonen/papers/curvetorsion.pdf)

Stoll's Selmer group Chabauty is relevant prior work on logarithm directions. At $p=2$, Proposition 2.8 compares the leading nonzero direction of a rational point's logarithm with the image of the global 2-Selmer group. Version 3 strengthens the kernel hypothesis (A3) to equality with the image of rational 2-primary torsion. The application fixes the auxiliary prime. Our question concerns the entire local logarithmic locus of a fixed curve as its good prime varies. Stoll's Lemma 1.1 also constructs torsion witnesses on other hyperelliptic models from the divisor of $y-h(x)$. [Stoll, Lemma 1.1, Assumption 2.6 and Proposition 2.8](https://arxiv.org/html/1912.05893v3)

Uniform rational-point bounds obtained by choosing an auxiliary prime and bounds on the number of local points within individual discs have different quantifiers from an occupied-disc bound uniform in the varying prime. In the literature reviewed here we found no general positive-rank $o(p)$ bound for this local locus when $r\le g-2$. There is a geometric special case: if $J$ admits a rational rank-zero quotient $A$ of dimension at least two, every local logarithmic Chabauty point projects to torsion in $A$. The image of the curve generates $A$ up to translation, hence cannot be an elliptic translate. Manin–Mumford makes its geometric torsion intersection finite and the map onto the image has finite fibres. This gives a fixed bound independent of $p$; Example 4.3 of the genus-three paper has such a quotient. [Stoll](https://arxiv.org/abs/1307.1773) · [Katz–Rabinoff–Zureick-Brown](https://arxiv.org/abs/1504.00694) · [Balakrishnan–Caro](https://arxiv.org/abs/2501.03483) · [Genus-three examples](https://arxiv.org/abs/1805.03361)

## The split Cartan curve at depth two

On $X_s^+(13)\simeq X_0^+(169)$ the genus, Jacobian rank and rational Néron–Severi rank are all three. Two independent trace-zero correspondence classes give simultaneous quadratic Chabauty equations. Their local data involve single and double Coleman integrals, Frobenius and Hodge corrections, and global height coefficients. Linearizing both suitable integral expansions gives the same compatibility test when the leading terms are affine. More general reductions use the common roots of the two reduced polynomials, with an identically vanishing reduction requiring more precision.

| Auxiliary prime | Occupied / all | Basis for count |
|---:|---:|---|
| 3 | 6/6 | Rational points already meet every disc. A two-chart QC run is also available. |
| 11 | 7/20 reported | The archived two-chart run reports seven points. Its output predates explicit precision tracking. |
| 17 | 7/20 proved | The published joint zero set consists of the seven rational points. |

The primes 7 and 11 used to construct the Hecke correspondences in the 17-adic calculation play a separate role from the auxiliary prime. Independent reduction of the two charts at 11 covers the twenty discs: two only on the first chart, ten only on the second and eight on both. A precision-controlled repetition of the 11-adic heights would upgrade the status of this computational check. [Three-adic transcript](https://github.com/steffenmueller/QCMod/blob/da975cf651fe14d92a8e13c2df21d4bd747d3efc/Examples/qc_Xs13plus.log#L28-L80) · [Eleven-adic transcript](https://github.com/steffenmueller/QCMod/blob/d754716d579f838afa86c8416a2e1a6da4e050c4/Examples/qc_Xs13plus.log#L23-L66) · [Seventeen-adic proof, §6](https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n3-p06-s.pdf)

For the usual rank-equals-genus construction with rational Néron–Severi rank two there is just one independent trace-zero height condition from that construction. This includes the generic rank-(1,1) bielliptic example with nonisogenous factors. Bianchi and Padurariu combine the two local heights in one function taking values in a finite set. A simple root on a given disc yields a zero of the tested function there by Hensel's lemma. A positive proportion of such discs as $p$ varies, and membership in the full depth-two locus, each require additional arguments. [Bianchi–Padurariu](https://arxiv.org/abs/2212.11635)

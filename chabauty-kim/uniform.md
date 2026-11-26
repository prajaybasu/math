# A uniform residue-disc bound at depth four

**Theorem.** Let $X=\mathbb P^1\setminus\{0,1,\infty\}$, let $q$ be an odd prime, and put $S=\{2,q\}$. For every prime $p\ge7$ outside $S$, the number of residues in $X(\mathbb F_p)$ attained by the **full refined depth-four locus** $X(\mathbb Z_p)^{\min}_{S,4}$ is $O(p/\log p)$. The implied constant is independent of $q$ and $p$. In particular this includes every auxiliary prime $p\ge7$ for $S=\{2,3\}$. The assertion counts occupied residue discs. Identifying the points within a disc requires additional information.

## Two exact equations

First consider the $(1,0)$ refinement of the depth-four polylogarithmic quotient. Put $L=\log(z)/p$ and $Y_m=p^{-m}\operatorname{Li}_m(z)$. There are equations
$$\alpha Y_2+\beta LY_1=0,\qquad A Y_4+B L Y_3+C L^3Y_1=0$$
over $K=\mathbb Q_p$, with $\alpha\ne0$ and $(A,B,C)\ne(0,0,0)$. In the depth-two equation the coefficient of $\operatorname{Li}_2$ is $\log(2)\log(q)\ne0$: both integers are units at $p$ of infinite multiplicative order. Lüdtke's Theorem 3.6 supplies a nonzero depth-four triple even if a particular determinantal formula gives the zero triple. Factors of $p$ of the same weight can be removed from each equation. Only existence of these coefficients is needed. [Lüdtke, Theorems 3.4 and 3.6](https://arxiv.org/html/2402.03573v2#S3.SS4)

## An integral lift of the finite-polylogarithm coordinates

Use independent variables $X,U_1,\ldots,U_4,T$, set $U_0=-X$, and define
$$D_m(T,U)=\sum_{j=0}^m U_{m-j}T^j/j!.$$
For a point of residue $a\ne0,1$, choose any $x\in\mathbb Z_p$ lifting $a$. Set $W_0=-x$, $W_m=(x-1)Y_m(z)$ and
$$u_m=\sum_{j=0}^m W_{m-j}(-L)^j/j!.$$
All entries are integral for $m\le4$ and $p\ge7$. Two different facts are needed:

1. The binomial theorem gives the **exact** identity $D_m(L,u)=W_m$. This defines the $u_m$ from actual Coleman values at the point.
2. Write $\ell_m(X)=\sum_{i=1}^{p-1}X^i/i^m\in\mathbb F_p[X]$. Besser's finite-polylogarithm reduction and the local expansions give $W_m\equiv D_m(\bar L,\ell(a))$. Indeed the constant values have residues $\ell_m(a)/(a-1)$, the local weight-zero term has residue $a/(1-a)$, and $(a-1)a/(1-a)=-a$. Inverting the triangular translation in the residue field gives $u_m\equiv\ell_m(a)$.

The $u_m$ can vary within a disc. Their residues depend only on $a$. This allows an identity over $K$ to be normalized before passing to the residue field, even if its coefficients share many factors of $p$. [Besser, Propositions 2.1 and 2.3](https://arxiv.org/pdf/math/0006051) · [Uniform local Taylor estimate](../lean/BBPGrouping/MirimanoffLocalExpansion.lean)

## A nonzero polynomial of degree at most six

In $K[X,U_1,\ldots,U_4][T]$ set
$$F=\alpha D_2+\beta T D_1,\qquad G=A D_4+B T D_3+C T^3D_1.$$
Their degrees in $T$ are at most two and four. Form $P=\operatorname{Res}_T(F,G)$ **using their actual degrees over the coefficient ring**. Every coefficient of either polynomial in $T$ is linear in $(X,U_1,\ldots,U_4)$. Each term in the Sylvester determinant therefore has total degree at most six in these five variables.

Here is a specialization proving $P\ne0$ for all allowed coefficients. Set $X=U_1=U_2=1$ in this formal polynomial ring. This specialization serves only to test polynomial nonvanishing. It gives
$$F_*(T)=\alpha+(\alpha+\beta)T-(\alpha/2+\beta)T^2.$$
It preserves the degree of $F$: when its quadratic coefficient vanishes, its linear coefficient is $\alpha/2\ne0$. Also $F_*(0)=\alpha$ and $F_*(1)=3\alpha/2$, so its roots in an algebraic closure form a finite set disjoint from $\{0,1\}$.

* If $A\ne0$, set $U_3=0$. At each root of $F_*$ the specialized $G$ is affine in $U_4$ with slope $A$. Choose $U_4$ outside the finite set of forbidden values.
* If $A=0$ and $B\ne0$, at a root $r$ the slope in $U_3$ is $Br\ne0$. Choose $U_3$ in the same way.
* In the remaining case $C\ne0$ and $G_*(T)=CT^3(1-T)$. Its two possible roots have already been excluded.

Thus the specialized polynomials have no common root. The product formula for the resultant is the leading coefficient of $F_*$ raised to the original $T$-degree of $G$, times the product of $G_*(r)$ over the roots of $F_*$ with multiplicity. This is nonzero even if the degree of $G$ drops upon specialization. The generic resultant is consequently nonzero.

At any actual common Coleman zero, $(X,U,T)=(x,u,L)$ makes both polynomials vanish by the exact translation identity. Consequently $P(x,u)=0$. This direction is valid even when degrees drop at the actual point, by the polynomial Bézout identity for the Sylvester determinant.

Choose a nonzero coefficient $c$ of $P$ of maximal $p$-adic norm. Then $P/c$ is integral with a unit coefficient, so $R=\overline{P/c}$ is nonzero of total degree at most six. For **every** disc occupied by this component,
$$R(a,\ell_1(a),\ell_2(a),\ell_3(a),\ell_4(a))=0.$$
No coefficient of either input equation needs to be a unit. Dividing a *finite-precision approximation* by an unknown power of $p$ would not justify this conclusion. Here the exact polynomial already vanishes on the integral lifts.

## Counting discs and passing to the total refined locus

Apply the mixed finite-polylogarithm root bound with $X$-degree and total $U$-degree each at most six. The proof imposes the differential conditions modulo one bounded-degree polynomial and uses Ghosh–Ward's mixed-polynomial nonvanishing lemma for the auxiliary polynomial. Its constants depend only on these degree bounds and the number of weights. This proves the uniform estimate for the $(1,0)$ component. [Counting argument](family.md#a-uniform-bound-on-the-number-of-candidate-discs) · [Ghosh–Ward, §3, Lemma 3](https://arxiv.org/pdf/1210.1893)

For the $(1,1)$ component Lüdtke's equations give $L=0$ and $Y_2=0$, hence $\ell_2(a)=0$. The same root estimate applies. Each full refined component is contained in its polylogarithmic component. The full quotient admits the $S_3$-action, whose six Möbius maps permute the residue discs for $p\ge7$. The two refinement types have six and three translates respectively. Adding their bounds gives the assertion for the total full refined locus. [Lüdtke, proof of Lemma 3.1 and Theorem 3.2](https://arxiv.org/html/2402.03573v2#S3.SS1)

Li–Lüdtke's Theorem 8.26 uses finite polylogarithms in an infinite-depth, imaginary-quadratic setting with a split auxiliary prime. It classifies possible pairs of roots of unity under their hypotheses. The argument above uses a fixed depth and bounds the number of occupied discs uniformly over the rational base field. [Li–Lüdtke, Theorem 8.26](https://arxiv.org/html/2608.20615v1#S8)

## Checks and proof status

Run `sage -python ordinary_check.py` from this directory. The script evaluates the actual depth-two equation and the $3,9$ anchor determinant for $S=\{2,3\}$ at seven ordinary primes. It checks containment of every disc with a rational common field root in the resultant zero set. It also checks a pair of exact equations at $p=17$ for which reducing the inputs first gives an identically zero resultant. Removing $17^2$ from the exact resultant gives a nonzero field constraint retaining the prescribed common zero. These examples test the elimination step. The asymptotic assertion follows from the proof above.

Lean checks inverse translation and its compatibility with reduction, the specialization separating the quartic from the quadratic roots, and primitive reduction of an arbitrary nonzero $p$-adic multivariate resultant while preserving all integral common zeros and the monomial support bound. The application of the Coleman formulas, the passage from specialization to the generic degree-six resultant, the auxiliary-polynomial construction and asymptotic estimate, and the component comparison are given here as mathematical arguments. [Formal statements](../lean/BBPGrouping/UniformDiscBound.lean)

## A sufficient rank estimate for a power saving

For $t\ge1$ let $V_t$ be the space of polynomials in $X,y_1,\ldots,y_4$ of $X$-degree at most $t^2$ and total $y$-degree at most $t$. Consider the linear map
$$J_{p,t}:V_t\longrightarrow\mathbb F_p[X]/(X^p),\qquad f\longmapsto f(X,\ell_1(X),\ldots,\ell_4(X))\bmod X^p.$$
If there is a constant $c>0$ for which $J_{p,t}$ is injective at $t=\lfloor c p^{1/12}\rfloor$ for all sufficiently large primes, then the depth-four bound improves to $O(p^{11/12})$. Indeed injectivity gives precisely the nonvanishing of the first $W$-coefficient in the [counting proof](family.md#a-uniform-bound-on-the-number-of-candidate-discs). All the other dimension and multiplicity steps there hold for this $t$, with $t^2<p$. Their root count is at most $1+129p/t$. A [differential zero estimate](zero-estimate.md) now gives this injectivity for $t$ of order $p^{1/8}$ with a sufficiently small constant, yielding $O(p^{7/8})$. The numerical tests below probe the larger dimension-ceiling range.

There is room in the target for this conjectural estimate: the source has dimension $(t^2+1)\binom{t+4}{4}\sim t^6/24$, whereas the target has dimension $p$. Injectivity is impossible once the source exceeds $p$. For $t\ge2$, Ghosh–Ward's Lemma 3 gives injectivity under the sufficient inequality $t^2 4^{4t}<p-1$. The [general-weight calculation](finite-s.md#counting-for-a-fixed-number-of-weights) checks the induction at small $X$-degrees. The question concerns the range beyond that inequality. [Ghosh–Ward, §3](https://arxiv.org/pdf/1210.1893)

### Ranks at the dimension ceiling

Write $D=(t^2+1)\binom{t+4}{4}$. The largest possible rank is $\min(D,p)$, so the unavoidable source nullity is $\max(D-p,0)$. For $t\ge1$ the two factors of $D$ are both greater than one, so no prime equals the ceiling exactly. Each row below pairs the nearest primes on either side. Entries are exact finite-field ranks of the full $D$ by $p$ coefficient matrix.

| $t$ | $D$ | Prime below | Rank | Prime above | Rank |
|---:|---:|---:|---:|---:|---:|
| 1 | 10 | 7 | 7 | 11 | 10 |
| 2 | 75 | 73 | 73 | 79 | 75 |
| 3 | 350 | 349 | 349 | 353 | 350 |
| 4 | 1190 | 1187 | 1187 | 1193 | 1190 |
| 5 | 3276 | 3271 | 3271 | 3299 | 3276 |
| 6 | 7770 | 7759 | 7759 | 7789 | 7770 |
| 7 | 16500 | 16493 | 16493 | 16519 | 16500 |

All 30 tested pairs attained the maximum rank. The sweep used the three nearest primes on each side for $1\le t\le4$ and the nearest prime on each side for $5\le t\le7$.

```sh
sage -python mixed_rank.py --ceiling 1 2 3 4 --neighbors 3
sage -python mixed_rank.py --ceiling 5 6 7
```

### An integer certificate for all primes at fixed t

The first $D+1$ Taylor coefficients give one calculation over $\mathbb Q$ that applies at every prime $p>D$. Construct them from $\sum_{j=1}^D X^j/j^k$ for $1\le k\le4$. Every denominator has prime factors at most $D$. Reduction modulo a prime $p>D$ therefore agrees through degree $D$ with the finite-polylogarithm calculation, even when $p=D+1$.

Set $a=t^2+1$. The $a$ pure monomials $1,X,\ldots,X^{a-1}$ give an identity block on coefficient indices $0,\ldots,a-1$, and vanish in all later indices. Complete this block to a square minor in two ways, using indices $a,\ldots,D-1$ or $a+1,\ldots,D$ for the remaining $D-a$ rows. Clear each of these rows' denominators using its least common denominator. Call the determinants of the two resulting lower-right integer blocks $d_0,d_1$. At every $p>D$, the clearing factors are units. A nonzero null vector would make both determinants vanish modulo $p$, forcing $p\mid\gcd(d_0,d_1)$.

Hence if the gcd has no prime factor larger than $D$, $J_{p,t}$ is injective for **every** prime $p>D$. All smaller primes can be checked by direct rank over the field. The generic implication from two integer minors is formalized in Lean. The determinants for these particular Taylor coefficients are computed in Sage with exact integer arithmetic. [Lean minor criterion](../lean/BBPGrouping/MixedRank.lean)

| $t$ | $D$ | Bit lengths of $\lvert d_0\rvert,\lvert d_1\rvert$ | Gcd after stripping primes $\le D$ | Primes $p\le D$ of rank $p$ |
|---:|---:|---:|---:|---:|
| 1 | 10 | 37, 37 | 1 | 4 of 4 |
| 2 | 75 | 9636, 9869 | 1 | 21 of 21 |
| 3 | 350 | 332544, 334400 | 1 | 70 of 70 |

Thus for $t=1,2,3$ and every prime $p$, the rank is exactly $\min(D,p)$. The checks can be reproduced with

```sh
sage -python mixed_rank.py --certify 1 2 3
```

At $t=2$, $p=109$ illustrates why the second minor matters. Using only coefficients of degrees $0$ through $74$ gives rank $74$ in dimension $75$. Adding the coefficient at degree $75$ gives rank $75$, also the rank modulo $X^{109}$. The unique apparent relation at the shorter precision has first nonzero coefficient at $X^{75}$.

For growing $t$ this gives an arithmetic target. If both minors can vanish over $\mathbb Q$, their gcd supplies no information. Otherwise, let $P_t$ be the largest prime divisor of their gcd exceeding $D$, with $P_t=1$ if there is none. A uniform bound $P_t\le C t^{12}$, together with a nonzero minor over $\mathbb Q$ for all sufficiently large $t$, would give injectivity at $t=\lfloor c p^{1/12}\rfloor$ for sufficiently small fixed $c>0$: then $p>D$ and $p>P_t$. This would imply the stated $O(p^{11/12})$ disc bound. An exceptional factor of these two minors can be tested using further coefficient indices. The fixed-$t$ verifications and boundary ranks leave the growth of $P_t$ open.

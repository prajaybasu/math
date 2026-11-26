# A polynomial zero estimate for finite polylogarithms

Fix $k\ge1$, a prime $p$ and $\ell_i(X)=\sum_{m=1}^{p-1}X^m/m^i\in\mathbb F_p[X]$. Let $P\in\mathbb F_p[X,y_1,\ldots,y_k]$ be nonzero, with $X$-degree at most $A$ and total $y$-degree at most $t$. Set
$$N=\binom{t+k}{k},\qquad H=NA+\binom N2.$$

**Zero estimate.** If $t<p$ and $H<p$, then some coefficient of $P(X,\ell_1,\ldots,\ell_k)$ of index at most $H$ is nonzero. In particular substitution into $\mathbb F_p[X]/(X^p)$ is injective on this degree box.

### 1. Differentiation at the origin

Write $K=\mathbb F_p(X)$ and use the two operators on the $y$ variables
$$E=\partial_{y_1},\qquad S=\sum_{i=2}^k y_{i-1}\partial_{y_i}.$$
Work with the scaled derivation
$$\Delta=X(1-X)\partial_X+X E+(1-X)S.$$
Modulo $X^p$, substitution $y_i=\ell_i(X)$ intertwines $\Delta$ with $X(1-X)d/dX$. For $i=1$ the exact identity is $X(1-X)\ell_1'=X-X^p$. For $i\ge2$ it is $X\ell_i'=\ell_{i-1}$. The scaled univariate derivation preserves every ideal $(X^m)$. Consequently if the substituted $P$ vanishes modulo $X^m$ for $m\le p$, the same is true for all its $\Delta$-iterates. This assertion uses polynomial representatives and entails no division in the truncated ring.

### 2. A stable row space and its smallest leading monomial

Represent $P$ by its coefficient row in the $N$ monomials in $y$ of total degree at most $t$. The same box contains $R_j=\Delta^jP$: applying $E,S$ preserves the upper bound on total degree, and the $X$-degree of $R_j$ is at most $A+j$.

Take the first $r$ independent rows $R_0,\ldots,R_{r-1}$ up to the *first* dependence $R_r\in W=\operatorname{span}_K(R_0,\ldots,R_{r-1})$. Then $1\le r\le N$. The Leibniz rule implies $\Delta W\subseteq W$, since differentiation of a rational coefficient gives another rational coefficient.

Give $y_i$ weight $i$, and order the columns in descending weight, breaking ties in any fixed way. Take the reduced row echelon form over $K$ and let $h$ be its last nonzero row, viewed as a polynomial in $y$. Its first nonzero coefficient is $1$. The corresponding monomial is the smallest possible leading monomial of any nonzero element of $W$, since every such leading column is a pivot column. Both $E$ and $S$ lower weight by one. In $\Delta h$ the leading coefficient differentiates to zero, and the operators on $y$ can introduce only smaller monomials. Thus $\Delta h=0$ by the choice of $h$.

Let $B$ be the square submatrix of the original $r$ rows on the pivot columns, and $q=\det B\ne0$. The reduced rows are obtained by left multiplication by $B^{-1}$. Every coefficient of $h$ is a ratio of an $r$-row minor to $q$. Every such determinant has degree at most
$$H_r=\sum_{j=0}^{r-1}(A+j)=rA+\binom r2\le H.$$
This bounds both numerator and denominator even if the cyclic row space is proper. A zero coefficient can be represented as $0/1$.

Lean constructs this row without computing a full echelon form. Choose the latest possible leading column $k$, normalize the row there, and restrict the original rows to columns through $k$. They remain independent: a linear combination that vanishes on this prefix vanishes everywhere by maximality of $k$. Any column basis of the restriction contains $k$, since the chosen row is zero at every earlier column. Its coefficients on that basis are therefore a single unit vector. Cramer's rule gives the numerator of each ambient coordinate by replacing one column of this minor. [Last-row construction and Cramer numerators](../lean/BBPGrouping/PolylogZeroEstimate.lean)

### 3. The two poles force a constant

In $K[y]$, divide the horizontal equation $\Delta h=0$ by $X(1-X)$. Let $h_w$ be the nonzero top weighted part of $h$. The weight-$w$ equation reads $\partial_X h_w=0$. Its coefficients are rational functions of numerator and denominator degree at most $H_r<p$. Such a function with derivative zero belongs to $\mathbb F_p$: in lowest terms $u/v$, the equation $u'v=uv'$ implies $v\mid v'$, hence $v'=0$ and $u'=0$. A polynomial of degree less than $p$ with zero derivative is constant. This step controls the larger constant field $\mathbb F_p(X^p)$ of $K$.

Suppose $w>0$. Allow $h_{w-1}=0$ when that weight is absent. Its equation is
$$\partial_X h_{w-1}=-\frac{Eh_w}{1-X}-\frac{S h_w}{X}.$$
At this point $Eh_w$ and $S h_w$ have coefficients in $\mathbb F_p$. The derivative of a rational function has zero residue at each finite point in every characteristic: in its Laurent expansion the only possible source of a term of degree $-1$ is the derivative of the constant term. Taking residues coefficientwise at $X=0$ and $X=1$ gives $S h_w=0$ and $E h_w=0$. The commutators $[\partial_{y_j},S]=\partial_{y_{j+1}}$ for $j<k$ now show that every partial derivative of $h_w$ vanishes. All monomial exponents are below $p$ since $t<p$, so $h_w$ is scalar. This contradicts $w>0$. Therefore $h$ is scalar in $y$, and its pivot coefficient gives $h=1$. The same residue calculation can be made entirely with polynomials: in lowest terms a denominator of degree less than $p$ with a zero of order $s>0$ gives a pole of order $s+1$ in the derivative, since $1\le s<p$. A derivative with at most simple poles is therefore regular there. This is the version checked in Lean.

### 4. Returning to polynomial coefficients

The adjugate formula for the last reduced row writes
$$q=\sum_{j=0}^{r-1} b_j(X)R_j(X,y),\qquad b_j\in\mathbb F_p[X].$$
Only this polynomial identity is evaluated in the truncated ring. If the substituted $P$ vanished modulo $X^{H_r+1}$, then all rows on the right would vanish to the same order by §1, since $H_r+1\le p$. The nonzero $q$ on the left has degree at most $H_r$. This contradiction proves the estimate, including when $q(0)=0$.

### 5. Consequences for occupied discs

For the four-weight test choose $A=t^2$ and $t=\lfloor c p^{1/8}\rfloor$ with a sufficiently small fixed $c>0$. Then $N=\binom{t+4}4$ and $H=O(t^8)<p$ for sufficiently large $p$. In the auxiliary-polynomial proof this gives nonvanishing of the first nonzero coefficient in powers of $W$ after $W=X^p$. The multiplicity step still uses $W=a^p=a$ at candidate residues. Its dimension inequality and multiplicity $t^2$ hold for this choice of $t$, and its degree bound gives at most $1+129p/t$ candidates. This yields $O(p^{7/8})$ occupied discs at depth four for $S=\{2,q\}$, uniformly in the odd prime $q$. [Four-weight count](family.md#a-uniform-bound-on-the-number-of-candidate-discs) · [Depth-four elimination](uniform.md)

More generally, for each fixed $k\ge2$, $H=O_k(t^{2k})$ when $A=t^2$. The same substitution proves the mixed finite-polylogarithm root bound $O_{k,h,d}(p^{1-1/(2k)})$ for a nonzero field constraint of $X$-degree at most $h$ and total $y$-degree at most $d$. The general counting argument gives degree at most $t^2+pbt+(p-1)t$ with $b$ depending only on $k,h,d$. Its dimension estimates require only sufficiently large $t$, and $r=t^2<p$. At fixed $s=|S|\ge1$, taking $k=2s$ for the refined locus or $k=4s$ for the unrefined one gives the exponents $1-1/(4s)$ and $1-1/(8s)$ respectively. [Finite-S proof and counting argument](finite-s.md#counting-for-a-fixed-number-of-weights)

The dimension ceiling would allow $t$ of order $p^{1/6}$ for $k=4$ and hence an $O(p^{5/6})$ bound if injectivity held throughout that range. The quadratic term in $N$ in the minor-degree bound is where the present argument loses that exponent. [Exact ranks near the ceiling](uniform.md#ranks-at-the-dimension-ceiling)

### Proof status and sources

Lean proves the matrix argument in §§2–4. Given independent polynomial rows, it constructs the normalized final pivot row and bounds its coefficients, including after reduction to lowest terms. It proves horizontality for a triangular differential action preserving the span, clears a polynomial row with the adjugate, and specializes the identity to prove nonvanishing at precision $H_r+1$. The combined theorem `nonvanishing_of_horizontal_constants` takes the derivative action on the generating rows and the classification of bounded horizontal rows as explicit hypotheses.

For the particular polylogarithm system, Lean checks the exact differential identities, the small-degree constant and pole lemmas, the joint residue invariants, and preservation of vanishing under scaled differentiation. Identifying the cyclic derivative rows with the ordered monomial coordinates, assembling the weight-by-weight horizontal classification from these lemmas, extending the generator substitution identities to arbitrary polynomials, and the application to disc counting are written steps. The use of differentiation and auxiliary polynomials for truncated polylogarithms goes back to Ghosh–Ward. Cyclic differentiation of polynomial linear forms also occurs in the characteristic-zero multiplicity literature. [Lean declarations](../lean/BBPGrouping/PolylogZeroEstimate.lean) · [Ghosh–Ward](https://arxiv.org/pdf/1210.1893) · [Fischler on Shidlovsky's multiplicity estimate](https://doi.org/10.1017/S1446788717000386)

# Occupied residue discs for a finite set of primes

**Theorem 1.1.** Let $X=\mathbb P^1-\{0,1,\infty\}$ over $\mathbb Q$, and let $S$ be a set of $s\ge1$ rational primes. For every auxiliary prime $p\notin S$, each of the following loci occupies $O_s(p/\log p)$ residue discs in $X(\mathbb Z_p)$:

* the full refined Chabauty–Kim locus at depth $2s$;
* the full unrefined Chabauty–Kim locus at depth $4s$.

The implied constants depend only on $s$. For instance, the refined bound applies to $S=\{2,3,5\}$ at depth six. It bounds how many residues can occur as reductions of local points. Exact determination of the points is a further question.

For $S=\varnothing$ the refined locus is empty. In the unrefined case the published depth-one result already bounds the locus by the two primitive sixth roots of unity. This treats the empty set at positive depth. [Betts–Kumpitsch–Lüdtke, Remark 5.21](https://arxiv.org/pdf/2305.09462#page=45)

Zehavi proves a dimension inequality yielding finiteness for smooth projective curves of genus at least two with a rational base point, at each odd prime of good reduction and sufficiently large depth. Here the curve is affine, the depth is fixed in terms of $s$, and the bound counts occupied residues as $p$ varies. [Zehavi, §1](https://arxiv.org/html/2611.18218v1#S1)

## The polynomial map

When $2\notin S$ the refined locus is empty by the local condition at two. Otherwise fix any one of the $3^s$ refinements. Betts, Kumpitsch and Lüdtke give two weight-one parameters for each prime of $S$ and one generator in each odd weight $3,5,\ldots,n-1$. On each refinement one of $x_\ell,y_\ell,x_\ell+y_\ell$ vanishes for each $\ell$. This leaves $s+(s-1)=n-1$ free affine parameters $v$. Their localisation formulas over $K=\mathbb Q_p$ give polynomials $L(v)$ and $Y_m(v)$ for the scaled coordinates $p^{-1}\log$ and $p^{-m}\operatorname{Li}_m$, respectively. The first has degree at most one and $Y_m$ has ordinary degree at most $m$ by the weight grading. These bounds apply after specialising all periods and allow any coefficients to vanish. [Betts–Kumpitsch–Lüdtke, Proposition 5.3, Theorem 5.6 and Proposition 5.11](https://arxiv.org/pdf/2305.09462)

Adjoin one independent variable $x$. Put $W_0=-x$ and $W_k=(x-1)Y_k(v)$ for $1\le k\le n$. Consider the polynomial map over $K$ with $n$ source variables $(x,v)$ and $n+1$ outputs
$$f=(x,u_1,\ldots,u_n),\qquad u_m=\sum_{j=0}^{m}W_{m-j}(-L(v))^j/j!.$$
Each output has degree at most $D=n+1$. This map undoes translation in the log coordinate using exact values at the point.

For $p>n+1$, an occupied disc with residue $a$ supplies an integral point of the image, with reduction $(a,\ell_1(a),\ldots,\ell_n(a))$, where $\ell_m(X)=\sum_{i=1}^{p-1}X^i/i^m$. Indeed choose $x\in\mathbb Z_p$ lifting $a$ and write the local point as $z=\zeta(1+pw)$ with $\zeta$ Teichmüller. Then $L(z)\equiv w\pmod p$. Besser's Proposition 2.1 gives $p^{-m}\operatorname{Li}_m(\zeta)\equiv\ell_m(a)/(a-1)$, and Proposition 2.3 translates these integral values by $w$ with coefficients $w^j/j!$. The weight-zero term, multiplied by $a-1$, is $-a$. Translation by $-L$ cancels translation by $w$ modulo $p$, since the coefficient in degree $k>0$ of their composite is $(w-\bar L)^k/k!$. A polynomial identity on a parametrised image holds on its Zariski closure as well, so the same reasoning applies to a scheme-theoretic localisation image. [Besser, Propositions 2.1 and 2.3](https://arxiv.org/pdf/math/0006051)

## A relation of uniform degree

Set $H=((n+1)D+1)^n$. Substitution along $f$ sends the space of polynomials of degree at most $H$ in each of $n+1$ variables into the space of degree at most $(n+1)DH$ in each of $n$ variables. The latter has dimension
$$((n+1)DH+1)^n\le H(H+1)^n<(H+1)^{n+1}.$$
There is consequently a nonzero kernel polynomial $P$ with each variable degree at most $H$. Divide by a coefficient of maximal $p$-adic norm before reducing. The resulting nonzero $R$ has the same degree bounds, and vanishes at the reductions of all integral image points. Source parameters can have arbitrary denominators. Thus every occupied disc of this refinement satisfies
$$R(a,\ell_1(a),\ldots,\ell_n(a))=0.$$
The degree bound can be very large even at depth six. It supplies uniformity as $p$ varies. [Lean proof of bounded dependence and primitive reduction](../lean/BBPGrouping/SelmerDiscBound.lean)

## Counting for a fixed number of weights

Here are the parameter changes in the [four-weight counting argument](family.md#a-uniform-bound-on-the-number-of-candidate-discs). Fix $n$, an $X$-degree bound $h$ and a total polylogarithm-degree bound $d$. In this application take $h=H$ and $d=nH$. For total polylogarithm degree $t$ the number of monomials is $N_t=\binom{t+n}{n}$. Use the derivation
$$\delta=X(1-X)\partial_X+(X-W)\partial_{y_1}
 +(1-X)\sum_{i=2}^n y_{i-1}\partial_{y_i},\qquad \delta W=0.$$
It acts as $X(1-X)d/dX$ on substituting $(W,y)=(X^p,\ell(X))$. Its applications preserve the upper bound on total $y$-degree and increase total $(X,W)$-degree by at most one.

Choose $A=r=t^2$, $B=bt$ with a fixed integer $b>3nd+h+1$. Look for a polynomial with degree bounds $A,B,t$ in $X,W,y$ respectively. For each $j<r$ impose that $(\delta^j\Phi)|_{W=X}$ be divisible by $R$. Write $E=A+B+r$. Multiplication by $R$ injects the space of degrees $(E-h,t-d)$ into the output space of degrees $(E,t)$. For sufficiently large $t$ the codimension is at most
$$(E+1)(N_t-N_{t-d})+hN_{t-d}\le (3ndt+h)N_t.$$
Indeed $E+1\le3t^2$ eventually, and $N_t-N_{t-d}\le dn N_t/(t+1)$ by telescoping. All $r$ conditions together cost fewer than the $(A+1)(B+1)N_t$ input coefficients, so a nonzero auxiliary polynomial exists.

In §3, Lemma 3 of the arXiv version, Ghosh and Ward use $a(f)=\deg_X f$ and $c(f)=\max\sum_{i=1}^n i e_i$, where the maximum is over the $y$-exponent vectors of its nonzero monomials. Their stated hypotheses are $\max\{a(f),1\}4^{c(f)}<p-1$ and $0<\max_i\deg_{y_i} f<p$. Their conclusion gives $X^p\nmid f(X,\ell_1(X),\ldots,\ell_n(X))$. The base $4$ is independent of $n$. [Ghosh–Ward, arXiv v1, p. 7](https://arxiv.org/pdf/1210.1893v1#page=7)

For the induction in that proof, use $M(a)=\max\{a,2\}$. The displayed estimate on p. 9 uses $(3a+2)/4\le\max\{a,1\}$, which fails at $a=1$. Their descent gives a nonzero polynomial with $a'\le 3a+2$ and $c'\le c-1$. Hence
$$M(a')\le4M(a),\qquad M(a')4^{c'}\le M(a)4^c.$$
Under $M(a)4^c<p-1$ every descent step satisfies the size hypothesis, the positive individual $y$-degrees are less than $p$ because they are bounded by $c$, and at weight zero the nonzero polynomial in $X$ has degree less than $p$. This verifies the numerical induction using the descent of Lemma 3. [Ghosh–Ward, arXiv v1, pp. 8–9](https://arxiv.org/pdf/1210.1893v1#page=8) · [Lean size estimates](../lean/BBPGrouping/SelmerDiscBound.lean)

Take $t=\lfloor\log p/(2n\log 4)\rfloor$. For sufficiently large $p$ we have $t\ge2$. In the first nonzero $W$-coefficient $f$, $M(a(f))\le t^2$, $c(f)\le nt$ and $\max_i\deg_{y_i}f\le t<p$. The floor gives $4^{2nt}\le p$. Since $t^2+2\le4^t\le4^{nt}$, we have $t^2 4^{nt}<p-1$, even with the strict cutoff. The strengthened size hypothesis therefore holds. For $f$ independent of the $y_i$, use $\deg_X f\le t^2<p$ directly. The first coefficient has order less than $p$ after substitution, so higher powers of $W=X^p$ cannot cancel it. The resulting nonzero univariate polynomial has degree at most $t^2+pbt+(p-1)t$. At each candidate residue $a\ne0,1$, all scaled derivatives through order $r-1$ vanish since $a^p=a$. Because $r<p$ and $a(1-a)\ne0$, the multiplicity is at least $r$. Degree divided by multiplicity gives $O_{n,h,d}(p/\log p)$ candidates. [Ghosh–Ward, §3, Lemma 3](https://arxiv.org/pdf/1210.1893)

Summing over the refinements multiplies the constant by at most $3^s$. The full locus maps into the polylogarithmic locus. Small auxiliary primes, including those with $p\le n+1$, are absorbed using at most $p-2$ discs. [Betts–Kumpitsch–Lüdtke, §4](https://arxiv.org/pdf/2305.09462)

The same proof bounds the **unrefined** full locus at depth $n=4s$ for $s\ge1$. The unrestricted polylogarithmic parameter count becomes $2s+(2s-1)=n-1$. There is one parametrisation and no sum over refinements. Both conclusions bound residue discs at fixed depth. Neither requires explicit period values or a period nonvanishing conjecture.

## Theorem 1.2. Power saving at fixed depth

Under the hypotheses of Theorem 1.1, the full refined locus at depth $2s$ occupies $O_s(p^{1-1/(4s)})$ discs and the full unrefined locus at depth $4s$ occupies $O_s(p^{1-1/(8s)})$. At $S=\{2,q\}$ the refined depth-four bound is $O(p^{7/8})$, uniformly in the odd prime $q$. For $n$ weights the differential zero estimate permits $t=\lfloor c_n p^{1/(2n)}\rfloor$ for small fixed $c_n$. The count above gives $O_{n,h,d}(p/t)$, and the degree bounds and number of refinements depend only on $s$. [Zero estimate and parameter choice](zero-estimate.md)

### An affine genus-two consequence

Let $C$ be the smooth projective model of $y^2=x^5-x$, and take $U$ to be the inverse image of $X$ under its hyperelliptic projection $x$. This deletes the three points over $0,1,\infty$. The six branch points of the double cover are distinct in every odd characteristic, so $C$ has genus two and good reduction away from two. The map $U\to X$ is finite of degree two over $\mathbb Z[1/2]$. The point $(-1,0)$ and its image provide compatible integral base points.

Take $S=\{2\}$ and any odd $p$. The morphism sends the full refined depth-two locus of $U$ into that of $X$. Indeed it induces a map on the class-two unipotent fundamental groups. The local Kummer maps commute with it at each place, so the local conditions defined by closures of Kummer images map into the corresponding conditions on $X$. Localisation then gives the asserted containment on loci. Over each occupied residue of $X$ the equation $y^2=x^5-x$ gives at most two residues of $U$. Thus the number of occupied discs on $U$ is $O(p^{3/4})$ at depth two by Theorem 1.2 with $s=1$. Filling the three punctures changes the fundamental group and the local conditions. The bound above counts discs of the entire affine refined locus.

A separate prior result for smooth projective curves applies when a Jacobian quotient of dimension at least two has rank zero and finite Tate–Shafarevich group and the curve has a rational base point. A fixed finite subscheme already contains the depth-one locus at good primes, giving a uniform constant bound in that setting. [Betts–Kumpitsch–Lüdtke, §5.7](https://arxiv.org/pdf/2305.09462)

## Theorem 1.3. The leading depth-four cofactor

For $S=\{2,3\}$, write $k=\log_p(2)/p$ and let $A$ be the normalised $\operatorname{Li}_4$ cofactor of the determinant anchored at $3,9$, with the row order and scaling specified in the proof. Then $9A\equiv52kB_{p-3}\pmod p$ for $p\ge7$. For $p\ne13$ the two causes of its vanishing are the base-two Wieferich congruence and divisibility of the numerator of $B_{p-3}$ by $p$. At $13$ the scalar $52$ vanishes. The base-three Wieferich case affects the valuation of $\log_p(3)$ in the equations. [Cofactor and Bernoulli calculation](wolstenholme.md) · [Base-three valuation analysis](family.md)

For the $(1,1)$ component, a primitive fourth root $i$ at a split prime $p\ge7$ passes both finite-field tests exactly when $p$ divides both Euler numbers $E_{p-3}$ and $E_{p-5}$. Meštrović's weight-two search and three weight-four evaluations exclude both primitive fourth roots throughout $7\le p<10^7$. The computations test the finite reductions. [Derivation and values](torsion.md#the-factor-for-primitive-fourth-roots) · [Meštrović](https://arxiv.org/abs/1212.3602)

## Theorem 1.4. Six exceptional auxiliary primes

For $S=\{2,3\}$, the full refined depth-four locus equals the 21 points of $X(\mathbb Z[1/6])$ at each of $11,1093,3511,16843,1006003,2124679$. Lüdtke's published range covers the first three. The certificates for $16843,1006003,2124679$ extend this conclusion to those three primes beyond that range. [Lüdtke, Theorem 1.2](https://arxiv.org/abs/2402.03573) · [Wolstenholme certificates](wolstenholme.md) · [Certificate for 1006003](README.md)

## Open problems

For four weights, injectivity of the truncated substitution map $J_{p,t}$ all the way to the dimension scale $t\asymp p^{1/6}$ with a small absolute constant would give $O(p^{5/6})$ occupied discs. The all-prime certificates for $t=1,2,3$ and exact ranks near the ceiling through $t=7$ address fixed test spaces. Uniform injectivity for growing $t$ at this scale remains open. [Rank certificates and numerical tests](uniform.md#ranks-at-the-dimension-ceiling)

For $(1,1)$ at depth four, a sufficient condition is that the extra finite-field common factors occur at a set of primes of Dirichlet density zero. Primitive fourth roots already give a simultaneous Euler divisibility test. Common factors surviving modulo $p$ may disappear at higher precision. The $(1,0)$ component requires a separate argument to determine the full locus. [Fixed-depth torsion criterion](torsion.md)

## Verification and related work

Lean checks the bounded-degree polynomial relation over any field, including the dimension comparison, and the primitive finite-field relation for integral image points at every prime. It also checks the numerical induction and strict degree cutoff used with Ghosh–Ward’s lemma. The Selmer parametrisation, Besser's reduction, their application to the polynomial map above, and the mixed finite-polylogarithm count enter the arithmetic conclusion through the written proof.

Elimination for motivic Kim functions at general $S$ is prior work. The present use of elimination is after specialising the localisation map at $p$ and adjoining a residue coordinate. Its output is a bound on the number of occupied discs. [Polylogarithmic motivic Chabauty–Kim and resultants](https://arxiv.org/abs/2408.07400)

Li–Lüdtke use finite polylogarithms to constrain pairs of roots of unity over imaginary quadratic fields in infinite depth under their stated hypotheses. Leonhardt–Rendell compute de Rham bases and Hodge filtrations from modular forms for quadratic Chabauty, including an explicit computation on the nonsplit Cartan modular curve of level 13. These results provide context for the finite-polylogarithm reduction and for higher-genus computations, respectively. [Li–Lüdtke, Theorem 8.26](https://arxiv.org/html/2608.20615v1#S8) · [Leonhardt–Rendell, §§4 and 6](https://arxiv.org/html/2610.30703v1#S4)

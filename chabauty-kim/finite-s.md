# Occupied residue discs for a finite set of primes

Let $X=\mathbb P^1-\{0,1,\infty\}$ and let $S$ be a finite set of rational primes. Write $s=|S|\ge1$. At depth $n=2s$ the number of residue discs occupied by the full refined Chabauty–Kim locus of $X$ is
$$O_s(p/\log p)$$
for auxiliary primes $p\notin S$. The constant depends only on $s$. For example $S=\{2,3,5\}$ has depth six in this statement. Exact determination of the points at that depth is a separate problem.

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

Take $t=\lfloor\log p/(2n\log 4)\rfloor$. For sufficiently large $p$ we have $t^2 4^{nt}<p-1$. In the first nonzero $W$-coefficient the $X$-degree is at most $t^2$ and the weighted $y$-degree is at most $nt$. Ghosh–Ward's mixed nonvanishing lemma shows that evaluation at $y=\ell(X)$ has order less than $p$ at zero (immediate by degree when this coefficient is independent of $y$). Higher $W$-coefficients cannot cancel it after $W=X^p$. The resulting nonzero univariate polynomial has degree at most $t^2+pbt+(p-1)t$. At each candidate residue $a\ne0,1$, all scaled derivatives through order $r-1$ vanish since $a^p=a$. Because $r<p$ and $a(1-a)\ne0$, the multiplicity is at least $r$. Degree divided by multiplicity gives $O_{n,h,d}(p/\log p)$ candidates. [Ghosh–Ward, §3, Lemma 3](https://arxiv.org/pdf/1210.1893)

Summing over the refinements multiplies the constant by at most $3^s$. The full locus maps into the polylogarithmic locus. Small auxiliary primes, including those with $p\le n+1$, are absorbed using at most $p-2$ discs. The empty $S$ case of the refined statement is vacuous by the local obstruction at two. [Betts–Kumpitsch–Lüdtke, §4](https://arxiv.org/pdf/2305.09462)

The same proof bounds the **unrefined** full locus at depth $n=4s$ for $s\ge1$. The unrestricted polylogarithmic parameter count becomes $2s+(2s-1)=n-1$. There is one parametrisation and no sum over refinements. Both conclusions bound residue discs at fixed depth. Neither requires explicit period values or a period nonvanishing conjecture.

## An affine genus-two consequence

Let $C$ be the smooth projective model of $y^2=x^5-x$, and take $U$ to be the inverse image of $X$ under its hyperelliptic projection $x$. This deletes the three points over $0,1,\infty$. The six branch points of the double cover are distinct in every odd characteristic, so $C$ has genus two and good reduction away from two. The map $U\to X$ is finite of degree two over $\mathbb Z[1/2]$. The point $(-1,0)$ and its image provide compatible integral base points.

Take $S=\{2\}$ and any odd $p$. The morphism sends the full refined depth-two locus of $U$ into that of $X$. Indeed it induces a map on the class-two unipotent fundamental groups. The local Kummer maps commute with it at each place, so the local conditions defined by closures of Kummer images map into the corresponding conditions on $X$. Localisation then gives the asserted containment on loci. Over each occupied residue of $X$ the equation $y^2=x^5-x$ gives at most two residues of $U$. Thus the number of occupied discs on $U$ is $O(p/\log p)$ at depth two. Filling the three punctures changes the fundamental group and the local conditions. The bound above counts discs of the entire affine refined locus.

A separate prior result for smooth projective curves applies when a Jacobian quotient of dimension at least two has rank zero and finite Tate–Shafarevich group and the curve has a rational base point. A fixed finite subscheme already contains the depth-one locus at good primes, giving a uniform constant bound in that setting. [Betts–Kumpitsch–Lüdtke, §5.7](https://arxiv.org/pdf/2305.09462)

## Verification and related work

Lean checks the bounded-degree polynomial relation over any field, including the dimension comparison, and checks the primitive finite-field relation for integral image points at every prime. The Selmer parametrisation, Besser's reduction, their application to the polynomial map above, and the mixed finite-polylogarithm count enter the arithmetic conclusion through the written proof.

Elimination for motivic Kim functions at general $S$ is prior work. The present use of elimination is after specialising the localisation map at $p$ and adjoining a residue coordinate. Its output is a bound on the number of occupied discs. [Polylogarithmic motivic Chabauty–Kim and resultants](https://arxiv.org/abs/2408.07400)

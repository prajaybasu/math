# Candidate discs at base-2 and base-3 Wieferich primes

Fix the thrice-punctured line over $\mathbb Z[1/6]$. Take a prime $p\ge7$ with
$3^{p-1}=1\pmod {p^2}$ and $2^{p-1}\ne1\pmod {p^2}$. There are two further unit tests below. The result applies at any positive valuation of $s=\log_p(3)/p$. This scale is nonzero since the only units in the kernel of the logarithm on $\mathbb Z_p^\times$ are roots of unity.

## Eliminating the local coordinate

Use $L=\log_p(z)/p$, $Y_m=p^{-m}\operatorname{Li}_m(z)$, $k=\log_p(2)/p$ and $d=Y_2(3)$. On the residue disc $a\ne0,1$ put
$$\ell_m(X)=\sum_{i=1}^{p-1}X^i/i^m,\qquad c_m=\ell_m(a)/(a-1),\qquad h=a/(1-a).$$
The local expansions give $Y_1\equiv c_1+hL$, $Y_2\equiv c_2+c_1L+hL^2/2$, and $Y_m\equiv c_m$ when $L\equiv0$. All reductions here are modulo $p$. [Local expansion and its hypotheses](README.md#from-the-coleman-equations-to-the-finite-screen) · [Besser, §2](https://arxiv.org/pdf/math/0006051)

Let $(A,B,C)$ be the cross product of the two rows $(Y_4(x),jY_3(x),j^3Y_1(x))$ for $(x,j)=(3,1),(9,2)$ in that order. The extra hypotheses are $d,C\in\mathbb Z_p^\times$. Their residues can be computed with the four finite polylogarithms since $L(3)=s$ and $L(9)=2s$ both reduce to zero. Also $k\equiv -(2^{p-1}-1)/p$ is a unit. At a common root the depth-two equation divided by $p^4$ and the depth-four determinant divided by $p^{12}s$ give
$$s kY_2+d L Y_1=0,\qquad s^3 A Y_4+s^2 B L Y_3+C L^3Y_1=0.$$
Indeed the raw determinant has rows $p^4(Y_4,LY_3,L^3Y_1)$ and the anchor rows have $L=js$. These are the previously published Coleman equations. [Lüdtke, Theorems 3.4 and 3.8 and Proposition 3.7](https://arxiv.org/abs/2402.03573)

Define $H(y)=A d^3y_1^2y_4-Bkd^2 y_1y_2y_3-Ck^3y_2^3$. Multiply the second equation by $d^3Y_1^2$, substitute the first, and cancel $s^3$ to obtain $H(Y)=0$. Multiplying the second equation by $d$, subtracting $CL^2$ times the first, and cancelling $s$ also gives $s^2AdY_4+sBdLY_3-CkL^2Y_2=0$.

* If $L\equiv0$, homogeneity gives $H(\ell_1(a),\ldots,\ell_4(a))=0$ over the residue field.
* If $L\not\equiv0$, the first equation and the last identity force $Y_1\equiv Y_2\equiv0$. Eliminating $L$ from their local expansions gives $Q(a)=0$, where $Q(X)=\ell_1(X)^2+2X\ell_2(X)$.

Both implications include discs on which $c_1=0$. On the $(1,1)$ component $\log z=0$ fixes the centre and $\ell_2(a)=\ell_4(a)=0$ is necessary. [Lean disc test](../lean/BBPGrouping/MirimanoffFamily.lean) · [Lüdtke, §3](https://arxiv.org/abs/2402.03573)

Write $b=v_p(\log_p 3)\ge2$. The raw cofactors are $p^8s^4 A,p^8s^3 B,p^8s C$. Their valuations are at least $(4+4b,5+3b,7+b)$, with equality in each entry precisely when its normalized cofactor is a unit. On the $L\equiv0$ branch of a nonsingular disc, $dY_1$ is a unit, so $L/s=-kY_2/(dY_1)$ is integral. Substituting this quotient into the determinant exhibits the common raw factor $p^{12}s^4$, of valuation $8+4b$. Individual terms can have higher valuation. On a singular disc the cubic excludes a **common** root whenever $c_2\ne0$, including when $b>2$.

## An exact criterion for sixteen lifts

Set $D=(X^{p-1}-1)/(X-1)$ and $T=H(\ell)Q\bmod D$. The monic $W=\gcd(D,T)$ has one simple factor per candidate disc on $(1,0)$. A Bézout identity $UD+VT=W$ bounds their number by $\deg W$. If $\gcd(D,\ell_1,\ell_2)=1$, every candidate has $c_1\ne0$ (at $c_1=0$ either test forces $c_2=0$). The normalized depth-two equation then reduces to $dL(c_1+hL)$. Its two roots are distinct with derivatives $\pm dc_1$, and each has a unique Hensel lift. This gives exactly $2\deg W$ simple depth-two classes to check. The derivative reduction follows also from $Y_m'=Y_{m-1}$ in $L$ and $Y_0\equiv h$. Lüdtke already gives the per-disc upper bound in this valuation regime. [Lüdtke, Proposition 5.2 and Lemma 5.5](https://arxiv.org/abs/2402.03573)

In particular, if $W$ divides
$$M=(X+3)(X+1)(X-2)(X-3)(X-9)(3X+1)(3X-1)(9X-1)$$
and the singular gcd is one, at most 16 lifts are required on $(1,0)$. The polynomial test can succeed or fail prime by prime. At both primes below $W$ is the monic associate of $M$ and the $(1,1)$ gcd is $X+1$.

| $p$ | $\deg\gcd(D,H)$ | $\deg\gcd(D,Q)$ | $\deg W$ | unresolved singular discs | $(1,0)$ lifts |
|---:|---:|---:|---:|---:|---:|
| 11 | 7 | 1 | 8 | 0 | 16 |
| 1,006,003 | 7 | 1 | 8 | 0 | 16 |

Run from this directory in SageMath. Each command verifies the Bézout identity, the union of the two branch factors and the splitting of the candidate polynomials.

```sh
sage -python family_budget.py 11
sage -python family_budget.py 1006003
```

## When the logarithm of two is exceptional

Now let $b=v_p(\log_p 2)\ge2$ and $v_p(\log_p 3)=1$, retaining $k=\log_p(2)/p$, $s=\log_p(3)/p$ and the unit condition on $d$. Here $s$ is a unit. The anchor values require the translated local expansions at $L=s,2s$. Since $Y_1(3)=-k$ and $Y_1(9)=-3k$, the third entries of the anchor rows are exactly $-k,-24k$. Hence $A=kA'$, $B=kB'$. The raw minor valuations are at least $(7+b,7+b,8)$, with equality when $A',B',C$ are units.

Eliminating $LY_1$ with the depth-two equation gives, after cancelling the nonzero $sk$,
$$s^2dA'Y_4+sdB'LY_3-CL^2Y_2=0.$$
Reduce this identity modulo $p$. Write $V_m(L)=(a-1)Y_m(L)$ in the residue field, so
$$V_m(L)=\sum_{j=0}^{m-1}\ell_{m-j}(a)L^j/j!-aL^m/m!.$$
The reduced depth-two equation is $dL(\ell_1(a)-aL)=0$ after multiplication by $a-1$. Evaluate
$$G(L)=s^2dA'V_4(L)+sdB'LV_3(L)-CL^2V_2(L)$$
at $L=0$ and $L=\ell_1(a)/a$. A common root must survive at least one of these two evaluations. This reasoning allows the two coordinates to coincide. [Lean cancellation and disc test](../lean/BBPGrouping/MirimanoffFamily.lean)

| $p$ | $(A',B',C)\bmod p$ | raw minor valuations | $(1,0)$ candidate residues | $(1,1)$ |
|---:|---|---|---|---|
| 1093 | $(236,198,598)$ | $(9,9,8)$ | $3,9,822,972,1090,1092$ | $-1$ |
| 3511 | $(2123,3162,1461)$ | $(9,9,8)$ | $3,9,3508,3510$ | $-1$ |

Run the same Sage commands with arguments 1093 and 3511. As a cross-check, evaluating the two unscaled anchor rows with the certificate’s Taylor series gives the same raw minor valuations at absolute precision 16 at each prime. In each example the only singular candidate is $-1$, where $Y_1(-1)=-k$. On this singular disc the two reduced classes coincide. The per-disc upper bound of two depth-two points still applies by Proposition 5.2, while a simple-root Hensel test requires a further subdivision there. Lüdtke's published range already covers the refined loci at both primes. [Lüdtke, Theorem 1.2](https://arxiv.org/abs/2402.03573)

## A uniform bound on the number of candidate discs

For any nonzero $R\in\mathbb F_p[X,y_1,\ldots,y_4]$ of $X$-degree at most six and total $y$-degree at most six, the number of $a\ne0,1$ with $R(a,\ell_1(a),\ldots,\ell_4(a))=0$ is $O(p/\log p)$ with an absolute implied constant. The coefficients may vary with $p$. Apply this to
$$R=y_2 H(y)(y_1^2+2Xy_2).$$
It is nonzero since $Ck^3$ is a unit. The zero set contains the candidates from both components at a base-3 exceptional prime. For the base-2 case with $A'ds$ a unit, use $R=y_2y_4X^3 G(y_1/X)$ with the displayed formula for $V_m$ over the polynomial ring, replacing $a$ by $X$ and $\ell_i$ by $y_i$. The factor $X^3$ clears all denominators. Its product with $G$ contains $s^2dA' X^3y_4$ with nonzero coefficient. The same degree bounds apply. This estimates the number of discs. The finite-field computation and the precision required for individual lifts are separate costs.

The proof adapts the auxiliary-polynomial method of Ghosh and Ward for individual finite polylogarithms. We use their mixed-polynomial nonvanishing lemma and impose differential conditions modulo $R$. [Ghosh and Ward, §3, Lemma 3](https://arxiv.org/pdf/1210.1893)

Choose an integer $t\ge256$ satisfying $t^2 4^{4t}<p-1$. Write $A_0=t^2$, $B_0=128t$, $r=t^2$ and $N_t=\binom{t+4}{4}$. The space of auxiliary polynomials $\Phi(X,W,y)$ with respective degree bounds $A_0,B_0,t$ (total degree for $y$) has dimension $(A_0+1)(B_0+1)N_t$. Use the derivation
$$\delta=X(1-X)\partial_X+(X-W)\partial_{y_1}
 +(1-X)\sum_{m=2}^4y_{m-1}\partial_{y_m},\qquad \delta W=0.$$
Under $W=X^p$, $y_m=\ell_m(X)$ this acts as $X(1-X)d/dX$ by direct differentiation of the defining sums.

For $0\le j<r$, impose that $(\delta^j\Phi)|_{W=X}$ be a multiple of $R$. Each output has $y$-degree at most $t$ and $X$-degree at most $E=A_0+B_0+r$, since each application increases total degree in $(X,W)$ by at most one. Multiplication by $R$ embeds the box with bounds $(E-6,t-6)$ in the output box $(E,t)$. Thus each condition costs at most $(E+1)N_t-(E-5)N_{t-6}$ linear constraints. Six successive differences of $N_t$ give $N_t-N_{t-6}\le24N_t/(t+1)$. Since $E+1\le3t^2$, the total rank is at most $t^2(72t+6)N_t$, strictly below the input dimension. Choose a nonzero solution $\Phi$.

The specialization $P=\Phi(X,X^p,\ell(X))$ is nonzero. Since $t\ge256$, the bound $t^2$ also covers the floor of two in the [numerical descent estimate for Lemma 3](finite-s.md#counting-for-a-fixed-number-of-weights). Take the least $W$-exponent with a nonzero coefficient $f(X,y)$. Its $X$-degree is at most $t^2$ and its weighted $y$-degree (weight $m$ on $y_m$) is at most $4t$. Lemma 3 of Ghosh and Ward implies $X^p\nmid f(X,\ell(X))$ if $f$ depends on $y$; the same follows from the degree if it only depends on $X$. Higher $W$-powers cannot cancel this first block.

At each root under consideration $a^p=a$, so the imposed conditions give $((X(1-X)d/dX)^jP)(a)=0$ for all $j<r$. Since $a(1-a)\ne0$ and $r<p$, a first nonzero Taylor coefficient of order $j<r$ would give a nonzero $j$th such derivative. Hence each root has multiplicity at least $r$. The degree of $P$ is at most $t^2+128pt+(p-1)t$, which bounds the root count by $1+129p/t$. For all sufficiently large primes, $t=\lfloor\log(p)/(8\log 4)\rfloor$ satisfies the size conditions. Enlarging the absolute constant covers the remaining primes.

Lean proves elimination, the resulting disc test, simplicity of the two reduced classes, the Bézout bound, and the dimension-to-root-count implication given specialization and multiplicity hypotheses. The differential construction, the application of the published nonvanishing lemma, and the asymptotic parameter choice above are paper proofs. The numerical Bézout computations run in Sage. Lean also checks the two anchor rows and all candidate residues at $p=11$ directly from the finite sums. [Lean statements](../lean/BBPGrouping/MirimanoffFamily.lean)

## Related Chabauty–Kim results

Corwin, Dan-Cohen and Lüdtke prove the original level-four conjecture for the same ring and all primes $5\le p<1000$. Their Theorem 5.21 uses two functions involving multiple polylogarithms. Its proof computes the required integration constants from ordinary polylogarithms at $S_3$-transforms, a potential use for batched ordinary-polylogarithm evaluation. The present certificate uses the refined equations. [Corwin–Dan-Cohen–Lüdtke, §5.7](https://arxiv.org/html/2610.25365v2#S5.SS7)

Li and Lüdtke give explicit loci over quadratic fields. In Theorem 8.26, equations (8.29)–(8.32), they already use Besser’s reduction to finite polylogarithms to constrain Teichmüller coordinates. The weights $p-2,p-3$ yield the exact inverse-pair condition in their infinite-depth argument. This is prior art for using finite polylogarithms as a sieve in Chabauty–Kim theory. Their Theorems 1.3 and 1.4 exhibit roots of unity that persist in polylogarithmic loci, even after symmetrisation in some cases. These give a concrete obstruction to transferring the eight-disc pattern to a new ground field. Zehavi's dimension inequality concerns smooth projective curves of genus at least two at sufficiently large depth. [Li–Lüdtke, Theorems 1.3, 1.4 and 8.26](https://arxiv.org/html/2608.20615v1) · [Zehavi, §1](https://arxiv.org/html/2611.18218v1#S1)

# Depth four at the base-3 Wieferich prime 1,006,003

For the thrice-punctured line over $\mathbb Z[1/6]$, take $S=\{2,3\}$ and $p=1{,}006{,}003$. The two depth-four polylogarithmic refined loci are

| Refinement | Points |
|---|---|
| $(1,0)$ | $-3,-1,3,9$ |
| $(1,1)$ | $-1$ |

Lemma 3.1 of Lüdtke identifies the total refined depth-four locus with the 21 integral points once these two component equalities are known. Theorem 1.2 covers $5\le p<10{,}000$. The calculation here treats a single prime. [Lüdtke, *Refined Chabauty–Kim computations*, §§3 and 6](https://doi.org/10.1007/s40993-024-00597-4)

## Reproduce the calculation

Run from this directory with SageMath 10.9. The input to `--digits` is the absolute precision of the depleted polylogarithms at the surviving centres.

```sh
work=$(mktemp -d)
sage -python certificate.py --digits 8 --lifts "$work/sage.jsonl"
cmp lifts.jsonl "$work/sage.jsonl"
```

A second all-disc evaluation uses a polynomial subproduct tree in FLINT. Build with a 64-bit FLINT 3 installation and its headers and library on the compiler and loader paths. Sage compares the two evaluations entry by entry and the two implementations' lists for each sieve branch.

```sh
cc -O2 -std=c11 check_screen.c -lflint -o "$work/check_screen"
sage -python certificate.py --digits 12 --verify-screen "$work/check_screen" --lifts "$work/checked.jsonl"
cmp lifts.jsonl "$work/checked.jsonl"
```

A separate Python program recomputes the lifts using integer arithmetic, a direct logarithm for weight one, modular integration of the higher weights, and Newton iteration. It requires NumPy and gmpy2. Absolute precision $K$ here refers to the **raw** equations. The two programs share the Coleman measure formula. They produce the same 16 sorted JSON lines, including the first nonzero depth-four digit for each exclusion.

```sh
python3 check_lifts.py 1006003 26 > "$work/lifts26.jsonl"
python3 check_lifts.py 1006003 32 > "$work/lifts32.jsonl"
cmp lifts.jsonl "$work/lifts26.jsonl"
cmp lifts.jsonl "$work/lifts32.jsonl"
```

To check the Lean declarations, run `lake exe cache get` and `lake build` from `../lean`.

## From the Coleman equations to the finite screen

Use the Coleman logarithm with $\log(p)=0$. For a residue $a\ne0,1$, let $\zeta$ be its Teichmüller lift, $L=\log(z)/p$, $Y_m=p^{-m}\operatorname{Li}_m(z)$, and $c_m(a)=p^{-m}\operatorname{Li}_m(\zeta)\bmod p$. Write $h=a/(1-a)$. The field polynomials evaluated by both programs are

$$c_m(a)=(a-1)^{-1}\sum_{i=1}^{p-1}a^i/i^m,\qquad 1\le m\le4.$$

Besser's Proposition 2.1 gives the depleted finite-polylogarithm formula. The factor $p^m/(p^m-1)$ restores the Coleman value at a Frobenius-fixed centre. Proposition 2.3 gives the local reduction in $w=(z/\zeta-1)/p$. Since $\log(1+pw)/p\equiv w\pmod p$, the same reduction holds in $L$. Its coefficients at weights one and two are $Y_1\equiv c_1+hL$ and $Y_2\equiv c_2+c_1L+hL^2/2$. At $L\equiv0$ it gives $Y_m\equiv c_m$ for all four weights. [Besser, *Finite and p-adic polylogarithms*, Propositions 2.1 and 2.3](https://arxiv.org/pdf/math/0006051)

The following substitutions instantiate `BBPGrouping.mirimanoff_sieve_sound`. All quotients in the middle column lie in $\mathbb Z_p$.

| Lean inputs | Certificate quantities | Verification |
|---|---|---|
| `a`, `ha0`, `ha1` | $a=2,\ldots,p-1$ | Both evaluators cover all $p-2$ discs. |
| `l2`, `l3`, `c23` | $\log(2)/p$, $\log(3)/p^2$, $\operatorname{Li}_2(3)/p^2$ | Their residues are $947598,297443,64338$. For the last equality use $L(3)\equiv0$. |
| `A`, `B`, `C` | Signed cofactors of the first row of Lüdtke's determinant, divided by $p^{12},p^{11},p^9$, respectively | Leading residues are $566848,944784,123582$ in row order $z,3,9$. |
| `hY1` through `hY4` | Reductions of the four scaled Coleman functions on the disc | The local expansion above applies uniformly since $p>5$. |
| `hf2`, `hf4` | The two raw equations at a common root | Substitute the scaled coefficients into Lüdtke's depth-two equation and Theorem 3.8. |

The exact local expansions can also be read directly from the Coleman differential equation. Put $D=x\,d/dx$, $R=x/(1-x)$, and $b_j=(D^jR)(\zeta)$. The operator $D$ preserves $\mathbb Z_p[x,(1-x)^{-1}]$, so every $b_j$ is integral and $b_0\bmod p=h$. In $x=\zeta\exp(pL)$ the function $Y_0$ has Taylor coefficients $p^j b_j/j!$. The relation $dY_m/dL=Y_{m-1}$ then gives

$$Y_m(L)=\sum_{i=0}^{m-1}Y_{m-i}(0)\frac{L^i}{i!}+\sum_{j\ge0}b_j\frac{p^j L^{j+m}}{(j+m)!}.$$

This expansion holds on the entire integral $L$-disc. For $j\ge1$, Legendre's bound gives $v_p((j+m)!)<(j+m)/(p-1)$. At this prime and weights $m\le4$ the terms with $j\ge1$ thus vanish modulo $p$ and tend uniformly to zero. The constants $Y_i(0)$ come from the Coleman measure at the Teichmüller centre. The theorem `BBPGrouping.mirimanoff_sieve_from_local_expansion` takes these exact Coleman expansions as hypotheses. Lean proves their uniform tail bound and derives the four field congruences and the sieve conclusion. [Local-expansion proof](../lean/BBPGrouping/MirimanoffLocalExpansion.lean) [Besser, §2](https://arxiv.org/pdf/math/0006051)

The sieve theorem guarantees that every common root lies on an unresolved singular disc, on the $L\equiv0$ branch, or on the $Y_1\equiv0$ branch. The eight singular discs all have $c_2\ne0$ and are excluded. The $L\equiv0$ branch leaves $3,9,335334,670669,894225,1006000,1006002$. The other branch leaves $2$. For $(1,1)$, $\log z=0$ forces $z=\zeta$. The necessary test $c_2=c_4=0$ leaves only $a=p-1$. Its lift $-1$ belongs to this component by the inclusion of its integral points. [Lean sieve theorems](../lean/BBPGrouping/MirimanoffSieve.lean) · [Lüdtke, §§3.2 and 6](https://doi.org/10.1007/s40993-024-00597-4)

## Lifting and precision

The coefficient calculation at selected Teichmüller points uses Coleman's integral over the units, with measure $\mu_\zeta(a+p^e\mathbb Z_p)=\zeta^a/(1-\zeta^{p^e})$. Group by $i+pb$ and expand $(i+pb)^{-m}$ modulo $p^r$. The terms from index $j=r$ onward are divisible by $p^r$. Integrality of the measure preserves that bound under integration. The geometric moments of $b$ start with $(1-\zeta)^{-1}$ and satisfy the binomial shift recurrence. This supplies the centre value without treating the series at a root of unity as an ordinary convergent power series. [Measure formula in the proof of Besser's Proposition 2.1](https://arxiv.org/pdf/math/0006051) · [Finite identities and truncation bound](../lean/BBPGrouping/GroupedDilog.lean)

Lifting uses $t=(z-\zeta)/p$. In the unscaled variable $z-\zeta$, multiplying by $1/z$ has integral coefficients. Integrating a term through index $k$ loses at most $\lfloor\log_p k\rfloor$ digits at each weight. Starting with $\operatorname{Li}_0=z/(1-z)$ and substituting $z-\zeta=pt$ gives coefficient valuation at least $k-m\lfloor\log_p k\rfloor$ for weight $m$. For $n+4\le p$, all terms of degree $k\ge n$ vanish modulo $p^n$. Differentiation in the integral coordinate $t$ preserves the error ideal. The Sage checker caps each polynomial at the minimum of this tail precision and its tracked coefficient precisions before normalization.

On the eight remaining discs the coefficient minima are $4,13$. Write $F_2=f_2/p^4$ and $F_4=f_4/p^{13}$. All 16 roots of $F_2\bmod p$ are simple, so each class has exactly one $p$-adic lift. Twelve have a nonzero $F_4$ digit. In each of the other four classes the known integral point is an exact common zero by the integral-point inclusion. Uniqueness of the $F_2$ lift then identifies the root. For example, on disc $2$ the depth-two root $z=2$ gives $F_4/p^2\equiv717943\pmod p$ and is excluded from $(1,0)$. [All 16 lifts](lifts.jsonl)

The same eight rational residue classes occur at the base-3 Wieferich prime 11. A finite-field criterion explains when sixteen depth-two lifts suffice for the entire $(1,0)$ component. [Family criterion and candidate-disc bound](family.md)

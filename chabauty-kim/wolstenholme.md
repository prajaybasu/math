# The depth-four refined locus at the Wolstenholme primes

For $X=\mathbb P^1\setminus\{0,1,\infty\}$, $S=\{2,3\}$ and each prime in
$$\{11,1093,3511,16843,1006003,2124679\},$$
the depth-four refined Chabauty–Kim locus is $X(\mathbb Z[1/6])$, the 21 integral points. The set comprises the two known examples in each of the base-2 Wieferich, base-3 Wieferich and Wolstenholme families. The theorem is about these six primes. Lüdtke's Theorem 1.2 gives the cases $11,1093,3511$. The companion certificate gives $1006003$. The two computations below give $16843$ and $2124679$. [Lüdtke, Lemma 3.1 and Theorem 1.2](https://doi.org/10.1007/s40993-024-00597-4) · [Certificate at 1006003](README.md) · [Wieferich prime search](https://cs.uwaterloo.ca/journals/JIS/VOL14/Klyve/klyve3.pdf) · [Wolstenholme primes](https://ems.press/content/serial-article-files/45540)

## Why the determinant factors

Use the normalizations and ordered anchor rows from the [family criterion](family.md). Write $k=\log_p(2)/p$, $s=\log_p(3)/p$, $d=\operatorname{Li}_2(3)/p^2$, $Y_m(x)=\operatorname{Li}_m(x)/p^m$ and $Z=\zeta_p^{\rm Col}(3)/p^3$, with the Coleman normalization of the trilogarithm period. Since the third anchor entries are $-k,-24k$, the normalized cofactor of $\operatorname{Li}_4$ is
$$A=2k(Y_3(9)-12Y_3(3))=-\tfrac{52}{3}kZ.$$
The second equality follows from duplication at 3 and $Y_3(-3)-2Y_3(3)=-13Z/6$. Duplication at 1 gives $Y_3(-1)=-3Z/4$. [Corwin–Dan-Cohen–Lüdtke, §5.7, equation (5.21)](https://arxiv.org/html/2610.25365v2#S5.SS7)

For $p\ge7$, Besser's formula gives $Y_3(-1)\equiv-\tfrac12\sum_{j=1}^{p-1}(-1)^j/j^3\pmod p$. The full reciprocal-cube sum is zero by summing powers in $\mathbb F_p^\times$, so the alternating sum is $\tfrac14\sum_{i=1}^{(p-1)/2}i^{p-4}$. The power-sum formula expresses this last sum without its factor $1/4$ as $(B_{p-3}(1/2)-B_{p-3})/(p-3)$ modulo $p$. All Bernoulli denominators here are prime to $p$. Using $B_m(1/2)=(2^{1-m}-1)B_m$ yields $-2B_{p-3}$ for the half sum. Thus
$$9A\equiv52 k B_{p-3}\pmod p.$$
For $p\ge7$, $p\ne13$, this vanishes exactly when $p$ is base-2 Wieferich or divides the numerator of $B_{p-3}$. At 13 the numerical coefficient itself vanishes. [Besser, Proposition 2.1](https://arxiv.org/pdf/math/0006051) · [Bernoulli criterion for Wolstenholme primes](https://ems.press/content/serial-article-files/45540)

## Certificate

For a disc $a\ne0,1$ use $L=\log_p(z)/p$, $h=a/(1-a)$ and $c_m=Y_m(\zeta_a)\bmod p$. The normalized depth-two polynomial is
$$u L^2+v L+w,\qquad (u,v,w)=(h(ks/2+d),\ c_1(ks+d),\ ks c_2).$$
At both primes $u\ne0$ on every disc. Both primes are $3\bmod4$, so the quadratic formula tests all classes from the discriminant (including zero). The reduced determinant at $A=0$ gives the second field test
$$L\big(s^2 B Y_3(L)+C L^2 Y_1(L)\big)=0.$$
The local expansions supply both $Y_m(L)$ and the derivative of the reduced quadratic. Their coefficientwise precision and the higher-precision Taylor estimates are given in the [certificate notes](README.md#lifting-and-precision).

| $p$ | Discs tested | Depth-two classes | Common classes | Singular common classes | $f_4(2)/p^{13}\bmod p$ |
|---:|---:|---:|---:|---:|---:|
| 16,843 | 16,841 | 16,692 | 5 | 0 | 14,351 |
| 2,124,679 | 2,124,677 | 2,124,776 | 5 | 0 | 1,644,662 |

Each common class contains one of $-3,-1,2,3,9$, verified by reducing its actual logarithm. The simple derivative gives exactly one depth-two root in each class. The four integral points $-3,-1,3,9$ are exact common roots by the integral-point inclusion. The remaining depth-two root is exactly 2 since $\operatorname{Li}_1(2)=\operatorname{Li}_2(2)=0$. The last column excludes it from the depth-four locus using the raw determinant of Lüdtke's equation (6.2), with rows $z,3,9$. On $(1,1)$ the logarithm forces $z=\zeta_a$ and the necessary test $c_2=c_4=0$ leaves just $a=-1$. The point $-1$ belongs to this component. Lemma 3.1 now gives the stated equality. [Lüdtke, §§3 and 6](https://arxiv.org/html/2402.03573v2#S3)

Run from this directory with SageMath 10.9 and 64-bit FLINT 3. The comparison checks every entry of all four field tables against a separate subproduct-tree evaluation. The lifts use direct sums at the five selected centres. At eight depleted digits the raw determinant at 2 has absolute precision 20 for both primes.

```sh
work=$(mktemp -d)
cc -O2 -std=c11 check_screen.c -lflint -o "$work/check_screen"
for p in 16843 2124679; do
    "$work/check_screen" --tables-only "$p" "$work/field.bin" &&
    sage -python wolstenholme.py "$p" --field-table "$work/field.bin" || exit 1
done
```

Lean checks the cofactor algebra given the period and harmonic-sum identities, the two-factor equivalence with unit coefficients, the local reduction given the stated expansions and equations, and the discriminant equivalence. The Coleman identities, Bernoulli calculation and Hensel argument above connect these declarations to the executable certificate. Sage and FLINT perform the numerical evaluations. [Lean declarations](../lean/BBPGrouping/WolstenholmeSieve.lean)

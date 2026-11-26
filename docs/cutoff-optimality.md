# Cutoff Optimality for Binary Machin-Type BBP Formulas (and Base-10 Exclusion)

In `euler_grouped`, the largest odd denominator is $M_{\max} = \frac{2}{3}n$—33% smaller than Bellard's $n$ and 67% smaller than original BBP's $2n$. This note proves that **$c = \frac{2}{3}$ is strictly optimal** among all binary Gaussian (Machin-type) BBP formulas for $\pi$, and documents the remaining open problem of extending Borwein–Borwein–Galway (2004) to general (non-Machin) base-10 BBP formulas.

---

## Part I: Quantitative BBG for $\mathbb{Q}(i)$ — $\frac{2}{3}n$ is optimal

### Setup

Every binary BBP-type arctangent / Gaussian-logarithm term over $\mathbb{Q}(i)$ comes from expanding $\operatorname{Im}\log(1 + z)$ at a point $z \in \mathbb{Q}(i)$ whose modulus is a half-integer power of $2$:

- **Type A** ($z = i / 2^r$, $r \ge 1$): $\arg(1 + i/2^r) = \arg(2^r + i)$, $|z| = 2^{-r}$, prime cutoff $c = \frac{1}{r}$.
- **Type B** ($z = \pm (1+i) / 2^r$, $r \ge 1$): $\arg(1 \pm (1+i)/2^r) = \pm\arg((2^r \pm 1) + i)$, $|z| = 2^{-(r - 1/2)}$, prime cutoff $c = \frac{2}{2r - 1}$.

Write $\alpha_r = 2^r + i$ and $\beta_r^\pm = (2^r \pm 1) + i \in \mathbb{Z}[i]$. The set of all binary Gaussian generators with cutoff strictly below $\frac{2}{3}$ is

$$
\mathcal{G}_{< 2/3} = \{\alpha_r : r \ge 2\} \;\cup\; \{\beta_r^+, \beta_r^- : r \ge 3\}.
$$

### Theorem 1 (Quantitative BBG for base 2)

Every $\mathbb{Z}$-linear relation
$$
\sum_{\gamma \in S} n_\gamma \arg(\gamma) = q\pi \qquad (S \subset \mathcal{G}_{< 2/3}\text{ finite},\; n_\gamma \in \mathbb{Z},\; q \in \mathbb{Q})
$$
has $q = 0$ and is a $\mathbb{Z}$-linear combination of the Aurifeuillean zero-relations
$$
\arg(\alpha_{2r-1}) + \arg(\beta_r^+) - \arg(\beta_r^-) = 0 \qquad (r \ge 3).
$$
In particular, **no** binary Gaussian (Machin-type) BBP formula for $\pi$ achieves cutoff $c < \frac{2}{3}$. The minimum $c = \frac{2}{3}$ is achieved by Euler/Hutton's identity
$$
(3 + i)^2(7 + i) = 50(1 + i) \iff 2\arg\!\left(1 - \frac{1-i}{4}\right) + \arg\!\left(1 - \frac{1-i}{8}\right) = \frac{\pi}{4}.
$$

### Proof

**Step 1 (Eliminate $\alpha_{2r-1}$ for $r \ge 3$).** In $\mathbb{Z}[i]$,
$$
\beta_r^+ \cdot \overline{\beta_r^-} = (2^r + 1 + i)(2^r - 1 - i) = 2^{2r} - 2i = 2\,\overline{\alpha_{2r-1}} \qquad (r \ge 1).
$$
Since $\arg(\beta_r^+), \arg(\beta_r^-), \arg(\alpha_{2r-1}) \in (0, \pi/4)$ for $r \ge 2$, taking principal arguments gives $\arg(\alpha_{2r-1}) + \arg(\beta_r^+) - \arg(\beta_r^-) = 0$ in $\mathbb{R}$. Substituting $\arg(\alpha_{2r-1}) = \arg(\beta_r^-) - \arg(\beta_r^+)$ for every $r \ge 3$ leaves a relation with the same $q\pi$ over the reduced generator set
$$
\mathcal{G}' = \{\alpha_{2k} : k \ge 1\} \;\cup\; \{\alpha_3\} \;\cup\; \{\beta_r^+, \beta_r^- : r \ge 3\}.
$$

**Step 2 (Disjoint cyclotomic levels).** Assign each $\gamma \in \mathcal{G}'$ a level $M(\gamma)$:
- $M(\alpha_{2k}) = 4k$ ($k \ge 1$): odd norm $N(\alpha_{2k}) = 2^{4k} + 1$.
- $M(\alpha_3) = 6$: odd norm $N(\alpha_3) = 2^6 + 1 = 5 \cdot 13$.
- $M(\beta_r^\pm) = 4r - 2$ ($r \ge 3$): setting $m = r - 1 \ge 2$,
  $$
  N(\beta_r^-) = 2 L_m, \qquad N(\beta_r^+) = 2 M_m,
  $$
  where $L_m = 2^{2m+1} - 2^{m+1} + 1$, $M_m = 2^{2m+1} + 2^{m+1} + 1$, $L_m M_m = 2^{4m+2} + 1$, and $\gcd(L_m, M_m) = 1$ (since $M_m - L_m = 2^{m+2}$ and both are odd).

Notice that the three families have **pairwise disjoint** levels: $4k \equiv 0 \pmod 4$, $6$, and $4r-2 \equiv 2 \pmod 4$ with $4r-2 \ge 10$. Moreover, every odd prime dividing $N(\gamma)$ divides $2^{M(\gamma)} + 1$, hence divides $2^{2M(\gamma)} - 1$.

**Step 3 (Prime-divisor elimination in $\mathbb{Z}[i]$).** Clearing denominators of $q$ and using $\prod (\gamma/\bar{\gamma})^{n_\gamma} \in \mu_4$ (since $\mathbb{Q}(i)^\times \cap S^1 = \{\pm 1, \pm i\}$), fourth powers give the $\mathbb{Z}[i]$-identity
$$
\prod_{n_\gamma > 0} \gamma^{4 n_\gamma} \prod_{n_\gamma < 0} \bar{\gamma}^{4 |n_\gamma|}
= \prod_{n_\gamma > 0} \bar{\gamma}^{4 n_\gamma} \prod_{n_\gamma < 0} \gamma^{4 |n_\gamma|}.
$$
Suppose an odd prime $p$ divides $N(\gamma_0) = a_0^2 + 1$ for one $\gamma_0 = a_0 + i \in S'$, and $p \nmid N(\gamma)$ for every other $\gamma \in S'$. Define the ring homomorphism
$$
\varphi : \mathbb{Z}[i] \to \mathbb{Z}/p\mathbb{Z}, \qquad x + yi \mapsto (x - a_0 y) \bmod p
$$
(well-defined since $(-a_0)^2 = a_0^2 \equiv -1 \pmod p$). Then $\varphi(\gamma_0) = 0$, $\varphi(\overline{\gamma_0}) = 2a_0 \not\equiv 0 \pmod p$ (as $p$ is odd and $p \nmid a_0$), and for every $\gamma \neq \gamma_0$, $\varphi(\gamma)\varphi(\bar{\gamma}) = N(\gamma) \bmod p \neq 0$, so both $\varphi(\gamma)$ and $\varphi(\bar{\gamma})$ are nonzero in the field $\mathbb{Z}/p\mathbb{Z}$. Applying $\varphi$ to the $\mathbb{Z}[i]$-identity forces $n_{\gamma_0} = 0$.

**Step 4 (Induction on $M_{\max}$).** Suppose $S' \subset \mathcal{G}'$ is nonempty with all $n_\gamma \neq 0$, and let $M_{\max} = \max_{\gamma \in S'} M(\gamma)$.
- **$M_{\max} = 4k \ge 4$ ($\gamma_0 = \alpha_{2k}$):** Since $2M_{\max} = 8k \ge 8 > 6$, Zsigmondy's theorem (1892) gives a primitive prime divisor $p$ of $2^{8k} - 1$. Then $p \mid 2^{4k} + 1 = N(\alpha_{2k})$ and $p \nmid 2^{2M} - 1$ for all $M < 4k$, so $p \nmid N(\gamma)$ for all other $\gamma \in S'$. Step 3 gives $n_{\alpha_{2k}} = 0$, contradiction.
- **$M_{\max} = 4r - 2 \ge 14$ ($m = r - 1 \ge 3$, generators $\beta_r^+, \beta_r^-$):** By Schinzel's theorem (1962, Theorem 2) on Aurifeuillean factors of $2^{4m+2} + 1 = L_m M_m$, for every $m \ge 3$ *both* $L_m$ and $M_m$ possess a primitive prime divisor of $2^{8m+4} - 1$. (Concretely, the cyclotomic Aurifeuillean factors $\Phi_{4(2m+1)}^\pm(2)$ satisfy $\Phi_{4(2m+1)}^\pm(2) > 2m+1$ for all $m \ge 3$, whereas any non-primitive prime dividing $\Phi_{4(2m+1)}(2)$ divides $2m+1$ to at most the first power; the only exceptions are $m = 1$, where $\Phi_{12}^+(2) = 1$, and $m = 2$, where $\Phi_{20}^+(2) = 5$.) Since $\gcd(L_m, M_m) = 1$, these two primitive primes are distinct and divide no $N(\gamma)$ at level $< 4r-2$. Step 3 forces $n_{\beta_r^+} = n_{\beta_r^-} = 0$, contradiction.
- **$M_{\max} \le 10$ ($S' \subseteq \{\beta_3^+, \beta_3^-, \alpha_3, \alpha_2\}$):** The odd norms are $41$, $5^2$, $5 \cdot 13$, and $17$. Applying Step 3 in order to $p = 41$ (kills $\beta_3^+$), $p = 17$ (kills $\alpha_2$), $p = 13$ (kills $\alpha_3$), and $p = 5$ (kills $\beta_3^-$) forces all $n_\gamma = 0$.

Hence $S' = \emptyset$, so $q = 0$. $\square$

The Lean 4 module [`lean/BBPGrouping/CutoffOptimality.lean`](../lean/BBPGrouping/CutoffOptimality.lean) formalizes Steps 1–3, the finite elimination $M_{\max} \le 10$, the Euler/Hutton identity $(3+i)^2(7+i) = 50(1+i)$, and the full reduction to Zsigmondy (1892) and Schinzel (1962).

---

## Part II: Open Problem — General (Non-Machin) Base-10 BBP Exclusion

### What Borwein–Borwein–Galway (2004) proved

In *Finding and Excluding $b$-ary Machin-Type Individual Digit Formulae* (Canad. J. Math. 56(5), 2004), Borwein, Borwein, and Galway proved that $\pi$ has **no Machin-type BBP formula** in any base $b$ that is not a power of $2$ (in particular, no base-10 Machin-type BBP formula).

### What remains open

A general degree-1 base-$b$ BBP formula for $\pi$ has the form
$$
\pi = \sum_{k=0}^{\infty} \frac{1}{b^k} \sum_{j=1}^{m} \frac{a_j}{mk + j}, \qquad a_j \in \mathbb{Q}.
$$
Expanding in partial fractions over the $m$-th roots of unity gives
$$
\pi = -\frac{1}{m} \sum_{r=0}^{m-1} \left(\sum_{j=1}^{m} a_j \zeta_m^{-jr} b^{j/m}\right) \log\!\left(1 - \zeta_m^r b^{-1/m}\right).
$$
Whether any such identity exists for **$b = 10$** (with arbitrary period $m$ and non-Machin coefficients $a_j \in \mathbb{Q}$) is still **open**.

### Why general base-10 exclusion is harder than Machin-type

1. **Non-abelian Kummer extensions:** For Machin-type formulas, the arguments $1 - \zeta_m^r b^{-1/m}$ lie in $\mathbb{Q}(i)$ (or more generally a cyclotomic field $\mathbb{Q}(\zeta_M)$ when $b^{1/m} \in \mathbb{Q}(\zeta_M)$, which for $b = 10$ requires $m \mid 2$, since $\sqrt{10} \in \mathbb{Q}(\zeta_{40})$ while $10^{1/d}$ for $d \ge 3$ generates a non-abelian extension $\mathbb{Q}(\zeta_d, 10^{1/d})$).
2. **Algebraic linear combinations of logs:** In a general BBP formula, the coefficients $\lambda_r = \sum_{j=1}^m a_j \zeta_m^{-jr} 10^{j/m}$ are *algebraic* (not rational), so Baker's theorem guarantees $\mathbb{Q}$-linear independence of logs of multiplicatively independent algebraic numbers, **not** $\overline{\mathbb{Q}}$-linear independence (which requires Schanuel's conjecture, or careful Galois-descent to a $\mathbb{Q}$-linear relation via the trace/norm!).
3. **Abelian slice vs. general $m$:**
   - **Tractable first milestone (cyclotomic / abelian slice):** When $10^{b_0/m} \in \mathbb{Q}(\zeta_M)$ (i.e., $b_0/m \in \frac{1}{2}\mathbb{Z}$, using $\sqrt{10} \in \mathbb{Q}(\zeta_{40})$), the logarithms live in a cyclotomic field and the same Zsigmondy + prime-ideal splitting method on $\Phi_d(10^s)$ applies.
   - **Full general-$m$ problem:** Requires proving that the Galois-conjugate sum $\sum_{r} \lambda_r \log(1 - \zeta_m^r 10^{-1/m})$ cannot collapse to $\pi$ for any $m \ge 3$. For fixed $m$, this reduces to checking whether the $S$-unit group generated by $\{1 - \zeta_m^r 10^{-1/m}\}$ in $\mathbb{Q}(\zeta_m, 10^{1/m})$ has any non-trivial Galois-equivariant relation mapping to $\pi$ — an open frontier between Baker's theorem, Zsigmondy-type primitive prime ideals in Kummer fields, and high-precision PSLQ exclusion.

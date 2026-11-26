# Lean formalization

The Lake package is `bbp_grouping`. The root module `BBPGrouping` re-exports the two modules below. Each public theorem lives in the `BBPGrouping` namespace. The build uses the checked-in toolchain and Mathlib revision.

## Prime-modulus identities and fractional CRT

[BBPSum.lean](../lean/BBPGrouping/BBPSum.lean)

| Lean name | Statement |
| --- | --- |
| `BBPGrouping.bbp_prime_one` | For a prime $p=8k+1$ and $n\ge 4k$, the powers $2^{n-4k}$ and $2^n$ coincide modulo $p$. |
| `BBPGrouping.bbp_prime_five` | For a prime $p=8k+5$ and $n\ge 4k$, $2^{n-4k}$ equals $-4\cdot 2^n$ modulo $p$. |
| `BBPGrouping.carry_identity` | For a positive modulus $d$, doubling the least residue of $2^n$ and subtracting the least residue of $2^{n+1}$ yields zero or $d$. |
| `BBPGrouping.crt_fraction_decomposition` | For positive coprime $u,v$ and integer $a$, the fraction $a/(uv)$ equals the two projected fractions, using the cofactor inverses modulo $u$ and $v$, plus an integer. |

The private lemma `two_pow_half` identifies $2^{\lfloor p/2\rfloor}$ in `ZMod p` with the quadratic character of 2, for prime $p\ne2$. It uses Mathlib’s Euler criterion and evaluation of the Legendre symbol at 2.

## Finite grouping and the cost model

[GroupedCount.lean](../lean/BBPGrouping/GroupedCount.lean)

| Lean name | Statement |
| --- | --- |
| `BBPGrouping.mem_maximalPrimePowers_iff` | The selected moduli are the positive powers $p^k$ for which some input denominator is divisible by $p^k$ and none is divisible by $p^{k+1}$. All input denominators are positive. |
| `BBPGrouping.grouped_assembly` | Any finite rational sum with integer numerators and positive denominators is equal to a sum with one fraction at each selected modulus, plus an integer. |
| `BBPGrouping.grouped_modular_assembly` | The same grouped coefficients work for every common power $b^e$. The original sum multiplied by $b^e$ differs by an integer from the grouped sum using residues $b^e\bmod q$. |
| `BBPGrouping.card_maximalPrimePowers_le_grouped_cost` | If every input denominator is positive and at most $X$, the number of selected moduli is bounded by the number of prime powers through $X$. |
| `BBPGrouping.termwise_cost_eq` | There are exactly $\lfloor(X+1)/2\rfloor$ positive odd denominators through $X$. |
| `BBPGrouping.grouped_cost_le_primeCounting_add` | For $X\ge 2$, the number of prime powers through $X$ is at most $\pi(X)+4\sqrt X\log X$, where $\pi(X)$ counts primes. |
| `BBPGrouping.grouped_cost_le` | For $X\ge 2$, the grouped budget is at most $72X/\log X$. |
| `BBPGrouping.grouped_cost_div_termwise_cost_tendsto_zero` | The ratio of the prime-power cutoff budget to the odd-denominator cutoff budget tends to zero as $X$ tends to infinity. |
| `BBPGrouping.odd_cutoff_moduli_ratio_tendsto_zero` | If the input contains every positive odd denominator through $X$, the ratio of the actual number of selected moduli to the odd-denominator cutoff budget tends to zero. |

The private lemma `crt_over_finset` extends fractional CRT to any finite set of pairwise coprime positive moduli, and `log_le_two_mul_sqrt` bounds $\log x \le 2\sqrt{x}$ for $x \ge 0$.

**Scope:** The cost model charges one modular exponentiation per selected modulus for a common power $b^e$, bounded by all prime powers up to the inclusive cutoff $X$ (compared against all odd denominators up to $X$). `bbp_prime_one` and `bbp_prime_five` cover only primes $p \equiv 1, 5 \pmod 8$ (the classic BBP shape); the Euler-criterion collapse used for the Euler/Hutton families at every odd prime, and the per-term reduction of $2^{-m_j k}$ to a common exponent, are not formalized. `grouped_modular_assembly` assumes integer numerators and one common power $b^e$. `carry_identity` is a standalone lemma not used elsewhere. Coefficient preparation, factorization, CRT arithmetic, fixed-point certification, analytic series identities for $\pi$, and C runtime/memory behavior are outside the formalization.

## Quantitative BBG cutoff optimality in $\mathbb{Q}(i)$

[CutoffOptimality.lean](../lean/BBPGrouping/CutoffOptimality.lean) (companion to [docs/cutoff-optimality.md](cutoff-optimality.md))

| Lean name | Statement |
| --- | --- |
| `BBPGrouping.euler_hutton_gaussian_identity` | $(3+i)^2(7+i) = 50(1+i)$ in $\mathbb{Z}[i]$ (attains cutoff $c = 2/3$). |
| `BBPGrouping.aurifeuillean_gaussian_identity` | $((2^r+1)+i)((2^r-1)-i) = 2(2^{2r-1}-i)$ for all $r \ge 1$. |
| `BBPGrouping.aurifeuillean_prod`, `aurifeuillean_coprime` | $L_m M_m = 2^{4m+2}+1$ and $\gcd(L_m, M_m) = 1$ for all $m$. |
| `BBPGrouping.gaussian_prime_elim` | If an odd prime $p$ divides $a_0^2+1$ and no other $a^2+1$ in $S$, then any Gaussian relation on $S$ has exponent $e(a_0) = 0$. |
| `BBPGrouping.base_case_le_10` | Unconditional elimination of all five reduced generators at levels $M \le 10$ ($\{9+i, 16+i, 7+i, 8+i, 4+i\}$ via primes $41, 257, 17, 13, 5$). |
| `BBPGrouping.reducedGen_norm_dvd` | Every reduced `< 2/3` generator at level $M$ has odd norm dividing $2^M + 1$. |
| `BBPGrouping.quantitative_bbg_reduced` | Full induction (Step 4): assuming `ZsigmondyFourK` and `SchinzelAuri` as explicit hypotheses, every Gaussian relation on any finite subset of the reduced `< 2/3` generators is identically zero. |

## Exceptional-prime (Mirimanoff) depth-4 Chabauty–Kim sieve

[MirimanoffSieve.lean](../lean/BBPGrouping/MirimanoffSieve.lean) · [MirimanoffLocalExpansion.lean](../lean/BBPGrouping/MirimanoffLocalExpansion.lean)

| Lean name | Statement |
| --- | --- |
| `BBPGrouping.mirimanoff_sieve_sound` | Over `ℤ_[p]` (`p ≠ 2`), every common $p$-adic root of the depth-4 Kim functions at a base-3 Wieferich prime satisfies one of the three finite-field sieve tests (unresolved singular `c1 = c2 = 0`, log-zero branch, or `Li₁`-zero branch). |
| `BBPGrouping.one_one_sieve_sound` | On the `(1, 1)` component (`L = 0`), any common root of $p^2 Y_2 = 0$ and $p^4 Y_4 = 0$ satisfies $c_2 = c_4 = 0 \pmod p$. |
| `BBPGrouping.local_tail_summable`, `local_tail_norm_le_inv_p` | For prime $p \ge 7$ and $m \le 4$, the local expansion tail $\sum_{k \ge 1} b_k \frac{p^k}{(k+m)!} L^{k+m}$ is uniformly summable in `ℚ_[p]` with ultrametric norm $\le p^{-1}$ for all $L \in \mathbb{Z}_p$. |
| `BBPGrouping.local_expansion_toZMod_Y1`..`Y4` | Derives `hY1–hY4` from the Coleman local power-series expansions in $L = \log_p(z)/p \in \mathbb{Z}_p$. |
| `BBPGrouping.mirimanoff_sieve_from_local_expansion` | End-to-end theorem combining `local_expansion_toZMod_Y1`..`Y4` with `mirimanoff_sieve_sound` (with the Coleman local expansions stated as explicit hypotheses). |

## Kernel and axiom checks

Run `lake build` in `lean/`. From that directory, the following prints the axiom dependencies of the public theorems:

```sh
lake env lean --stdin <<'LEAN'
import BBPGrouping

#print axioms BBPGrouping.bbp_prime_one
#print axioms BBPGrouping.bbp_prime_five
#print axioms BBPGrouping.carry_identity
#print axioms BBPGrouping.crt_fraction_decomposition
#print axioms BBPGrouping.mem_maximalPrimePowers_iff
#print axioms BBPGrouping.grouped_assembly
#print axioms BBPGrouping.grouped_modular_assembly
#print axioms BBPGrouping.card_maximalPrimePowers_le_grouped_cost
#print axioms BBPGrouping.termwise_cost_eq
#print axioms BBPGrouping.grouped_cost_le_primeCounting_add
#print axioms BBPGrouping.grouped_cost_le
#print axioms BBPGrouping.grouped_cost_div_termwise_cost_tendsto_zero
#print axioms BBPGrouping.odd_cutoff_moduli_ratio_tendsto_zero
LEAN
```

The dependencies are Lean’s standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

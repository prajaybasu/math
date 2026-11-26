# Method: Prime-power grouping for π digit extraction

To extract bits starting at 1-based position $n$, set $d = n - 1$ and compute $\{2^d \pi\} \in [0, 1)$. Any binary BBP-type series splits $2^d \pi$ into a finite modular head and a rapidly decaying tail. In the head, each fraction $a/m$ only matters modulo $1$, so $a$ can be reduced modulo $m$. In termwise extraction, the dominant cost is running one modular exponentiation $2^e \bmod m$ per denominator.

[Robert Smith's Euler/Hutton method](https://www.stylewarning.com/posts/faster-digit-extraction/) puts four terms over each odd denominator $M = 2k+1$, shares powers across them, and pairs eligible $M$ with $3M$ (evaluating both modulo $3M$). Prime-power grouping pushes this idea to the limit: every composite odd denominator is split into its exact prime powers, leaving one full modular exponentiation per odd prime $p$ up to the series cutoff, plus a small extra cost for the $O(\sqrt{n})$ higher prime powers (the scalar Euler/Hutton code spends two per prime power $p^e$, $e \ge 2$).

## Prime-power partial fractions

For coprime $u$ and $v$, CRT gives a partial-fraction split in $\mathbb{Q}/\mathbb{Z}$:

$$
\frac{a}{uv} \equiv
\frac{a v^{-1} \bmod u}{u}
+ \frac{a u^{-1} \bmod v}{v} \pmod{1}.
$$

Iterating over the prime-power factorization of each denominator projects every head term onto its exact prime powers: if $q = p^j \parallel M$ with $M = qu$, the $q$-component of $a/M$ has numerator $a u^{-1} \bmod q$.

In the Euler/Hutton series, the four shifted head powers have exponents $d + b_j - m_j k$ with $(b_j, m_j) \in \{(1,3), (-1,5), (-1,6), (-4,10)\}$, signs $s_j(k) = (-1)^{\lfloor k/2 \rfloor}$ for $j \in \{1,2\}$ and $(-1)^k$ for $j \in \{3,4\}$, and odd cutoffs $M_j = 2\lfloor(d+b_j)/m_j\rfloor + 1$ (when $d+b_j \ge 0$, else $0$). For each odd prime power $q$, the projected head fraction is $(2^d A(q) \bmod q)/q$, where

$$
A(q) \equiv \sum_{j=1}^{4}
\sum_{\substack{u\text{ odd},\ 1\le u\le M_j/q\\p\nmid u}}
s_j(k)\,2^{b_j-m_j k}\,u^{-1} \pmod q,
\qquad k = \frac{qu-1}{2}.
$$

Writing $u = 2t + 1$ gives $k = qt + (q-1)/2$. For a prime $q = p$, Euler's criterion collapses $2^{(p-1)/2} \equiv (2/p) \pmod p$ (determined by $p \bmod 8$), and Fermat's little theorem gives $2^{-m_j p t} \equiv (2^{-m_j})^t \pmod p$. So $2^d \bmod p$ factors out completely, and $A(p)$ is built with a short linear scan and modular multiplications:

- **Fast primes:** In the scalar code, $p > M_2$ leaves only family 1 with $u = 1$, giving $A(p) = 2(-1)^{(p-1)/2}$ (zero inversions, zero loop). The IFMA code starts its fast path at $p > M_1/3$ (where only $u=1$ occurs across all active families); scaling by 16 gives an integer coefficient $|16A(p)| \le 49$ with common power $2^{d-4}$.
- **Medium/small primes & prime powers:** The scalar code batches cofactor inversions (Montgomery's trick) and folds short periods when $4q\varphi(q)$ is smaller than the cofactor count. The IFMA code accumulates a numerator/denominator pair per lane for medium primes and folds the Fermat inverse into the powering chain, handling tiny primes and higher prime powers ($q = p^e$, $e \ge 2$) on a scalar path.
- **Bellard grouping:** [Bellard's seven-family formula](https://www.bellard.org/pi/pi_bin/pi_bin.html) uses the same partial-fraction split, lifting lower prime powers into the maximal power of each prime $\le n$ so each odd prime takes at most one query power. Because its cutoff is $M_{\max} = n$ rather than $\frac{2}{3}n$, it evaluates ~50% more primes than Euler/Hutton.

## Why the cutoff is 2n/3 for this family

The prime count—and therefore most of the work—scales with the series cutoff $M_{\max} = c \cdot n$: $c = 2$ for original BBP, $c = 1$ for Bellard, and $c = \frac{2}{3}$ for Euler/Hutton.

Euler/Hutton reaches $c = \frac{2}{3}$ because of the Gaussian integer identity

$$
(3 + i)^2 (7 + i) = 50(1 + i)
\implies 2\operatorname{Im}\log\!\left(1 - \frac{1-i}{4}\right) + \operatorname{Im}\log\!\left(1 - \frac{1-i}{8}\right) = \frac{\pi}{4},
$$

where $|(1-i)/4| = 2^{-3/2}$ ($c = \frac{2}{3}$) and $|(1-i)/8| = 2^{-5/2}$ ($c = \frac{2}{5}$). For $z = (1-i)/2^{m+1}$ the factor $1 - z$ has norm $2(2^{2m+1} - 2^{m+1} + 1)/4^{m+1}$, and $2^{2m+1} - 2^{m+1} + 1$ is one Aurifeuillean factor of $2^{4m+2} + 1 = (2^{2m+1} - 2^{m+1} + 1)(2^{2m+1} + 2^{m+1} + 1)$. It equals $5$ for $m = 1$ and $5^2$ for $m = 2$, which is what lets the two terms combine into a multiple of $1 + i$. For $m \ge 3$, Schinzel's theorem (1962; see the README references) gives each Aurifeuillean factor a primitive prime divisor of $2^{8m+4} - 1$. That prime is not $5$, so no further term of this shape cancels against the first two. 

This is the Gaussian-integer framework of Borwein, Borwein and Galway (2004), who introduce these generators $\operatorname{Im}\log(1-(1+i)2^{-m})$, derive the Euler/Hutton-type formulas for $\pi$ from factorizations of $2^m - 1 - i$, and use primitive prime factors to exclude formulas; the cutoff remark above is a small application of it, not a new result. See [docs/cutoff-optimality.md](cutoff-optimality.md) for the complete proof of optimality in $\mathbb{Q}(i)$ (with its Lean 4 formalization in `CutoffOptimality.lean`) and the open problem of general base-10 BBP exclusion. It is also an argument about one family: relations built from Gaussian factors $2^{m+1} - 1 \pm i$. It does not rule out faster binary formulas for $\pi$ in general. Binomial binary series (such as Gosper's $\sum (50k-6)/(2^k\binom{3k}{k})$) have both a larger cutoff ($\approx 0.799n$) and $\Theta(k/\log k)$ prime factors per denominator, blowing up prime-power grouping to $O(n^2/\log n)$.

## Operation counts

Direct Bellard uses $\approx 0.7d$ full modular powers; [Smith's $(M,3M)$ pairing](https://www.stylewarning.com/posts/faster-digit-extraction/#two-denominators-for-the-price-of-one) uses $\approx \frac{56}{135}d$ full powers ($\approx 2.41$ bits of offset per power). Grouped Euler/Hutton raises this to $\approx 31$ bits of offset per full power at $n = 4\cdot 10^9$:

| Operation | Euler/Hutton IFMA, $n=4\cdot10^8$ | Euler/Hutton IFMA, $n=4\cdot10^9$ | Smith $(M,3M)$, $n=4\cdot10^9$ |
| --- | ---: | ---: | ---: |
| Full query powers | 14,546,461 | 129,152,486 | 1,659,259,259 |
| Bits of offset per full query power | 27.5 | 31.0 | 2.41 |
| Bits of offset per fractional division | 27.5 | 31.0 | ~3.86 |
| Lane squarings per bit of offset | 1.02 | 1.01 | ~13 |
| Fermat inverses folded into query chain | 5.16 M | 45.5 M | 0 |
| Euclidean inversions (scalar path) | 6,540 | 24,943 | 0 |
| Coefficient-prep lane iterations | 129.5 M | 1,213 M | — |
| Odd sieve candidates | 133 M | 1,333 M | 0 |

At $n = 10^9$, Bellard's counting build recorded 699,999,998 direct query powers vs. 50,847,533 grouped query powers (plus 45,645 coefficient powers, 477.3 M cofactor slots, and 1.40 B modular multiplies during prep). Coefficient preparation and sieving account for why wall-clock speedups are smaller than the raw power-count ratio; see [benchmarks.md](benchmarks.md) for full counters and phase splits.

## Certification

Every modular fraction and retained tail term is rounded downward in 96-bit fixed point. If $S$ is the accumulated sum in units of $2^{-96}$ and $R$ is the number of rounded terms, truncating the tail below 1 ulp yields the rigorous enclosure $[S - 1, S + R + 1] \pmod{2^{96}}$. Bellard retains 11 tail rows (omitted tail $< 362 \cdot 2^{-111}/(1 - 2^{-10}) < 2^{-96}$); Euler/Hutton retains 36, 24, 20, and 14 tail terms across its four families.

IFMA accumulates vector fractions downward at 100 bits, merges workers, and truncates to 96 bits (adding 1 to $R$). A window is reported only if the lower and upper enclosure endpoints agree on all requested bits; otherwise the program exits with status 1 and `"window":null`.

## Memory and segmentation

Direct Bellard uses $O(1)$ memory per thread. Unsegmented Bellard grouping keeps a full least-factor table ($O(n)$ space, ~1.12 GiB at $n = 10^9$). All segmented implementations share only base primes up to $\sqrt{M_{\max}}$ and sieve in L1-sized per-thread segments (using a pre-sieved pattern for $\{3,5,7,11,13\}$ and 64-bit word masks for $\{17..61\}$ in both Euler/Hutton extractors), keeping peak RSS to 2–4 MiB through $n = 10^{10}$.

For segmented Bellard with $T$ workers and cofactor block size $B$, storage is $O(\sqrt{n} + T(\sqrt{n} + B))$; a scan of $L$ slots uses $\lceil L/B \rceil$ batch inversions.

## Limits

The Lean theorem bounds modular exponentiations in a cutoff model, not wall-clock time: sieving, cofactor scans, and inversions still run in $\Theta(n)$ word ops (plus $\Theta(n \log\log n)$ sieve bit-marks in the segmented Eratosthenes sieve).

| Path | Supported range & limits |
| --- | --- |
| Scalar Euler/Hutton | $n \ge 1$, $M_1 < 2^{31}$ ($n \lesssim 3.22 \cdot 10^9$). Up to 16 threads. |
| IFMA Euler/Hutton | $n \ge 20{,}000$, $M_1 < 2^{32}$ ($n \lesssim 6.44 \cdot 10^9$). Up to 128 threads. x86-64 AVX-512 IFMA + DQ. |
| Bellard direct / unsegmented grouped | $1 \le n \le 10^9$. Up to 10 threads. |
| Bellard segmented | $1 \le n \le 10^{12}$ (benchmarked through $10^{10}$). Up to 10 threads. Block size $1$–$2^{20}$ (default $2^{16}$). |
| Smith port (`smith_fast`) | Positive $n$ (64-bit fallback past $2^{31}$). Up to 16 threads. `smooth` supports $P \in \{1,3,5,7,11,13,17,19,23\}$. |

All paths accept widths of 1–64 bits and reject other arguments with exit status 2. Tuning knobs: the IFMA build reads `B0FRAC` (scalar/medium prime split, default 0.09) and `SEGEPS` (segment growth, default 0.01) from the environment; `smith_fast` also accepts `smooth32`, the P-smooth variant with tree moduli capped below $2^{31}$ so it stays on 32-bit arithmetic. Wider windows or larger positions increase the chance of an inconclusive enclosure at 96-bit precision.

# Benchmarks

All timings are end-to-end wall time (sieve, setup, threads, arithmetic, certification) for certified 32-bit windows at 1-based bit offset `n`.

## Euler/Hutton on AMD Ryzen 9 9950X

GCC 15.2 (`-O3 -march=native -pthread`), medians of 7 runs (16 cores / 32 hardware threads):

| Program | Starting bit | Threads | Median | Peak RSS | Full query powers |
| --- | ---: | ---: | ---: | ---: | ---: |
| Grouped IFMA | 400,000,000 | 16 / 24 / 32 | 18.3 / 15.2 / 13.5 ms | 2.5 MB | 14,546,461 |
| Grouped IFMA | 2,000,000,000 | 16 / 24 / 32 | 87.6 / 72.1 / 62.2 ms | 2.6 MB | 66,829,385 |
| Grouped IFMA | 4,000,000,000 | 16 / 24 / 32 | 177.5 / 144.3 / 124.5 ms | 2.8 MB | 129,152,486 |
| Grouped scalar | 400,000,000 / 2,000,000,000 | 16 | 190.8 / 681.9 ms | 2.2 MB | — |
| Scalar Smith port (`smith3m`) | 4,000,000,000 | 16 | 8.64 s | 1.9 MB | 1,659,259,259 |

At $4\cdot 10^9$ bits, IFMA CPU time splits as ~25% sieving, 22% fast-prime powers, 29% medium-prime prep, 22% medium-prime powering, and 1.5% scalar path. See [method.md#operation-counts](method.md#operation-counts).

| Hex position | [Smith IFMA](https://www.stylewarning.com/posts/faster-digit-extraction/#notes-on-a-high-performance-implementation) (32T, 48-bit, his machine) | Grouped IFMA (32T, 48-bit, Ryzen 9 9950X) | Window |
| --- | ---: | ---: |
| $10^8$ | 42.4 ms | 13.9 ms | `CB840E21926E` |
| $10^9$ | 410 ms | 122 ms | `5895585A0428` |

## Direct and grouped Bellard on Apple M4

Apple M4 (4P+6E, 16 GB RAM), Apple Clang 21 (`-O3`), medians of 3 serial runs. The two tables below and the segmented table share one session; the crossover and phase-profiling tables come from earlier sessions. Peak RSS was 1.12 GiB for unsegmented grouped and 1.78 MiB for direct.

Times in seconds; speedup is `direct / grouped`.

| Position | Direct 1 | Grouped 1 | Speedup 1 | Direct 10 | Grouped 10 | Speedup 10 | Window |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $10^6$ | 0.016834 | 0.00685621 | 2.46× | 0.00282162 | 0.00284663 | 0.99× | `b7ffd208` |
| $10^7$ | 0.199924 | 0.0686978 | 2.91× | 0.0352875 | 0.0194725 | 1.81× | `b67eeaa7` |
| $10^8$ | 2.57735 | 0.721421 | 3.57× | 0.430474 | 0.212515 | 2.03× | `518367d3` |
| $10^9$ | 31.7962 | 7.40017 | 4.30× | 5.16684 | 2.18935 | 2.36× | `9f047f95` |

Minimum–maximum across the three runs, in seconds.

| Position | Direct 1 | Grouped 1 | Direct 10 | Grouped 10 |
| --- | ---: | ---: | ---: | ---: |
| $10^6$ | 0.01493–0.02232 | 0.00678–0.006938 | 0.002801–0.002934 | 0.002818–0.002904 |
| $10^7$ | 0.1999–0.2002 | 0.06837–0.06951 | 0.03525–0.03547 | 0.01935–0.01955 |
| $10^8$ | 2.573–2.587 | 0.721–0.7248 | 0.4301–0.4305 | 0.2123–0.2134 |
| $10^9$ | 31.74–31.86 | 7.396–7.421 | 5.166–5.171 | 2.189–2.195 |

### Crossover

Each cell is a median of 21 runs. The single-thread crossover was between 24,000 and 25,000 bits, with the two methods effectively tied at 24,000. The ten-thread crossover was between 1.0 and 1.2 million bits. The interquartile ranges overlapped at 1.0 million and separated in favor of grouping at 1.2 million.

<details>
<summary>Crossover measurements</summary>

One thread, in microseconds.

| Position | Direct | Grouped | Speedup |
| --- | ---: | ---: | ---: |
| 1,000 | 4.46 | 15.38 | 0.29× |
| 3,000 | 16.83 | 34.21 | 0.49× |
| 5,000 | 31.46 | 52.04 | 0.60× |
| 10,000 | 73.25 | 96.88 | 0.76× |
| 15,000 | 120.71 | 137.42 | 0.88× |
| 20,000 | 170.50 | 181.38 | 0.94× |
| 21,000 | 163.42 | 169.75 | 0.96× |
| 22,000 | 172.92 | 176.21 | 0.98× |
| 23,000 | 182.50 | 184.75 | 0.99× |
| 24,000 | 192.08 | 192.79 | 1.00× |
| 25,000 | 201.71 | 197.58 | 1.02× |
| 26,000 | 211.33 | 204.38 | 1.03× |
| 27,000 | 220.88 | 211.50 | 1.04× |
| 28,000 | 230.54 | 219.33 | 1.05× |
| 29,000 | 240.12 | 228.42 | 1.05× |
| 30,000 | 276.88 | 257.88 | 1.07× |
| 40,000 | 395.75 | 344.92 | 1.15× |
| 60,000 | 635.92 | 493.87 | 1.29× |
| 80,000 | 896.58 | 667.96 | 1.34× |
| 100,000 | 1174.88 | 815.71 | 1.44× |
| 150,000 | 1877.04 | 1213.21 | 1.55× |
| 200,000 | 2638.96 | 1585.38 | 1.66× |
| 300,000 | 4176.54 | 2376.54 | 1.76× |
| 400,000 | 5846.33 | 3117.75 | 1.88× |
| 500,000 | 7473.67 | 3834.04 | 1.95× |

Ten threads, in milliseconds.

| Position | Direct | Grouped | Speedup |
| --- | ---: | ---: | ---: |
| 1,000 | 0.088 | 0.085 | 1.04× |
| 3,000 | 0.086 | 0.096 | 0.90× |
| 5,000 | 0.091 | 0.108 | 0.84× |
| 10,000 | 0.107 | 0.122 | 0.87× |
| 15,000 | 0.114 | 0.142 | 0.81× |
| 20,000 | 0.132 | 0.162 | 0.81× |
| 30,000 | 0.147 | 0.186 | 0.79× |
| 40,000 | 0.168 | 0.232 | 0.72× |
| 60,000 | 0.213 | 0.321 | 0.66× |
| 80,000 | 0.273 | 0.410 | 0.67× |
| 100,000 | 0.326 | 0.496 | 0.66× |
| 150,000 | 0.465 | 0.672 | 0.69× |
| 200,000 | 0.608 | 0.840 | 0.72× |
| 300,000 | 0.925 | 1.152 | 0.80× |
| 400,000 | 1.233 | 1.457 | 0.85× |
| 500,000 | 1.565 | 1.744 | 0.90× |
| 600,000 | 1.676 | 1.913 | 0.88× |
| 700,000 | 1.981 | 2.141 | 0.93× |
| 800,000 | 2.270 | 2.406 | 0.94× |
| 900,000 | 2.551 | 2.662 | 0.96× |
| 1,000,000 | 2.892 | 2.908 | 0.99× |
| 1,200,000 | 3.500 | 3.398 | 1.03× |
| 1,500,000 | 4.574 | 4.101 | 1.12× |
| 2,000,000 | 6.048 | 5.265 | 1.15× |
| 3,000,000 | 10.155 | 7.574 | 1.34× |
| 5,000,000 | 18.327 | 12.130 | 1.51× |

</details>

### Operation counts

These are exact single-thread counts from a separate `COUNT_OPS` build. Powers start with one seed reduction. Squares count the subsequent base-two squaring steps. Each path also rounds 77 tail contributions. At the measured widths of the operands, each nonzero head fraction is rounded using three quotient limbs.

| Position | Direct query powers | Direct squares | Grouped query powers | Grouped query squares | Grouped coefficient powers | Grouped coefficient squares |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| $10^6$ | 699,998 | 9,066,028 | 78,497 | 1,098,958 | 2,452 | 11,147 |
| $10^7$ | 6,999,998 | 114,255,976 | 664,577 | 11,962,386 | 6,304 | 39,056 |
| $10^8$ | 69,999,998 | 1,376,047,614 | 5,761,454 | 120,990,534 | 16,831 | 131,353 |
| $10^9$ | 699,999,998 | 16,048,380,744 | 50,847,533 | 1,220,340,792 | 45,645 | 429,006 |

Grouped preparation counts include the cofactor scan, its inversions, and geometric setup. Query evaluation adds one coefficient multiplication per query power. Direct uses one reciprocal setup per query power, and grouped uses one per visited prime power.

| Position | Prime powers visited | Slots | Euclidean inversions | Euclidean divisions | Generic modular multiplies | Dyadic divisions | Block sums | Sieve writes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $10^6$ | 78,715 | 564,663 | 30,376 | 128,303 | 1,672,332 | 427,861 | 507 | 421,502 |
| $10^7$ | 665,111 | 5,240,085 | 243,517 | 1,141,490 | 15,427,276 | 4,379,285 | 1,272 | 4,335,421 |
| $10^8$ | 5,762,833 | 49,696,175 | 2,062,643 | 10,476,743 | 146,167,815 | 44,371,224 | 3,284 | 44,238,545 |
| $10^9$ | 50,851,194 | 477,308,763 | 17,986,928 | 98,825,618 | 1,403,711,530 | 448,948,468 | 8,850 | 449,152,466 |

### Grouped phases

From an earlier session. Sieve times are end-to-end trial medians. Coefficient preparation and evaluation are single-thread estimates from a separate profiling build that sampled every 64th prime and subtracted measured timer overhead.

| Position | Sieve 1 (s) | Sieve 10 (s) | Coefficient prep 1 (s) | Power and sum 1 (s) |
| --- | ---: | ---: | ---: | ---: |
| $10^8$ | 0.129 | 0.125 | 0.329 | 0.220 |
| $10^9$ | 1.339 | 1.367 | 4.233 | 2.515 |

## Segmented Bellard & scalar Euler/Hutton on Apple M4

Medians of 3 serial runs, same session as the tables above; peak RSS from `getrusage`. The direct value at $10^{10}$ is a single run of the 64-bit widened direct baseline from an earlier session.

| $n$ | Threads | Segmented s | Grouped s | Direct s | Segmented MiB | Grouped MiB | Direct MiB | Window |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| $10^7$ | 1 | 0.0698838 | 0.0686978 | 0.199924 | 1.69 | 15.58 | 1.61 | `b67eeaa7` |
| $10^7$ | 10 | 0.02423 | 0.0194725 | 0.0352875 | 2.30 | 15.81 | 1.75 | `b67eeaa7` |
| $10^8$ | 1 | 0.708016 | 0.721421 | 2.57735 | 1.73 | 120.84 | 1.61 | `518367d3` |
| $10^8$ | 10 | 0.191496 | 0.212515 | 0.430474 | 2.34 | 121.08 | 1.77 | `518367d3` |
| $10^9$ | 1 | 7.21695 | 7.40017 | 31.7962 | 1.84 | 1,151.14 | 1.61 | `9f047f95` |
| $10^9$ | 10 | 1.35397 | 2.18935 | 5.16684 | 2.59 | 1,151.39 | 1.78 | `9f047f95` |
| $10^{10}$ | 1 | 100.61 | — | — | 2.36 | — | — | `8545ec60` |
| $10^{10}$ | 10 | 14.77 | — | 115.73 | 4.08 | — | 1.73 | `8545ec60` |

| $n$ | Segmented / grouped, 1 thread | Segmented / grouped, 10 threads | Direct / segmented, 1 thread | Direct / segmented, 10 threads |
| ---: | ---: | ---: | ---: | ---: |
| $10^7$ | 1.017× | 1.244× | 2.861× | 1.456× |
| $10^8$ | 0.981× | 0.901× | 3.640× | 2.248× |
| $10^9$ | 0.975× | 0.618× | 4.406× | 3.816× |
| $10^{10}$ | — | — | — | 7.835× |

At one billion bits and ten threads (same session, medians of 3 serial runs, all certifying `9f047f95`): scalar `euler_grouped` **0.872 s** (2.11 MiB peak RSS; 34,614,429 primes, 34,620,581 modexps), the Smith port `smith3m` **3.75 s** (1.80 MiB) and `smooth` with P=19 **3.08 s** (1.80 MiB). Grouped Euler/Hutton is 4.3× faster than the same-machine `smith3m` port, 1.55× faster than segmented Bellard and 5.9× faster than direct Bellard.

In an earlier profiling build at one billion bits and ten threads, original grouping spent a median 1.262 s in its sequential sieve. The segmented base sieve took 32 µs, and segment marking totaled 0.555 worker-seconds across ten concurrent workers. The one-thread marking total was 0.400 s. At ten billion bits, segmented trials ranged from 99.86 to 103.61 s on one thread and from 14.75 to 14.77 s on ten. An earlier ten-thread run with a 256-slot cofactor block reproduced the default block’s enclosure in 15.48 s at 2.86 MiB peak RSS.

### Cofactor block size

A counting build at $n=10^8$ visited 49,696,175 cofactor slots at every block size and gave the same enclosure.

| Block size in words | Batch inverses | Euclidean inversions | Euclidean divisions |
| ---: | ---: | ---: | ---: |
| 1 | 43,935,949 | 43,893,295 | 227,693,768 |
| 7 | 7,594,188 | 7,591,617 | 54,471,190 |
| 256 | 2,162,716 | 2,161,377 | 11,214,950 |
| 4,096 | 2,064,183 | 2,062,872 | 10,478,387 |
| 65,536 | 2,063,954 | 2,062,643 | 10,476,743 |

## Verification

- **Bellard (direct, grouped, segmented):** 990 MPFR-checked cases (positions 1–400, varied widths, up to $2^{24}$), all clean under UBSan. At $n=10^{10}$, segmented Bellard and an independent 64-bit direct implementation both certify `8545ec60`.
- **Euler/Hutton (scalar & IFMA):** 209 MPFR window checks from $2\cdot 10^4$ to $2^{26}$, 53 cross-checks between IFMA and scalar, and agreement at $4\cdot 10^9$ against `smith_fast`'s 64-bit path:

| Starting bit | Certified 32-bit IFMA window |
| ---: | --- |
| 400,000,000 | `01100101110000100000011100010000` |
| 1,000,000,000 | `10011111000001000111111110010101` |
| 2,000,000,000 | `01110011000100001001101000010011` |
| 4,000,000,000 | `00101100010010101010110000101101` |

For published hexadecimal reference windows, run the IFMA program at bit `4h+1` with width 48. [Bailey's BBP reference table](https://www.davidhbailey.com/dhbpapers/bbp-alg.pdf#page=5) starts at hexadecimal position `h`, so compare against its 12 interior digits.

| Hex digits skipped | 48-bit window in hexadecimal |
| ---: | --- |
| 1,000,000 | `6C65E52CB459` |
| 10,000,000 | `7AF5863EFED8` |
| 100,000,000 | `CB840E21926E` |
| 1,000,000,000 | `5895585A0428` |

### Repeat a cross-check

From the repository root, the following compares a 32-bit reference window with all three Bellard modes, scalar Euler/Hutton, and both scalar Smith modes. It requires `jq`.

```sh
(
  set -eu
  make -C c
  expected=10110111111111111101001000001000
  check() {
    result=$("$@")
    printf '%s\n' "$result" |
      jq -e --arg expected "$expected" '.certified and .window == $expected'
  }
  for mode in direct grouped segmented; do
    check ./c/bellard_bench "$mode" 1000000 32 4
  done
  check ./c/euler_grouped 1000000 32 4
  check ./c/smith_fast smith3m 1000000 19 32 4
  check ./c/smith_fast smooth 1000000 19 32 4
)
```

### Generate an independent MPFR window

With MPFR and GMP development headers and libraries on the compiler’s search path, build this temporary reference tool. The directed bounds derive the result directly from π at precision proportional to the requested position. Use it for manageable offsets. The reference prints a window only if both bounds yield the same integer after scaling and flooring.

```sh
(
  set -eu
  check_dir=$(mktemp -d)
  trap 'rm -r "$check_dir"' EXIT
  cc -O2 -x c - -lmpfr -lgmp -o "$check_dir/pi_window" <<'C'
#include <mpfr.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
    if (argc != 3)
        return 2;
    unsigned long n = strtoul(argv[1], NULL, 10);
    unsigned long width = strtoul(argv[2], NULL, 10);
    if (!n || !width || width > 64 || n > MPFR_PREC_MAX - 160)
        return 2;

    unsigned long shift = n + width - 1;
    mpfr_t bound;
    mpz_t lo, hi;
    mpfr_init2(bound, n + 160);
    mpz_inits(lo, hi, NULL);
    mpfr_const_pi(bound, MPFR_RNDD);
    mpfr_mul_2ui(bound, bound, shift, MPFR_RNDD);
    mpfr_get_z(lo, bound, MPFR_RNDD);
    mpfr_const_pi(bound, MPFR_RNDU);
    mpfr_mul_2ui(bound, bound, shift, MPFR_RNDU);
    mpfr_get_z(hi, bound, MPFR_RNDD);

    int certified = mpz_cmp(lo, hi) == 0;
    if (certified) {
        for (unsigned long bit = width; bit > 0; --bit)
            putchar(mpz_tstbit(lo, bit - 1) ? '1' : '0');
        putchar('\n');
    }
    mpz_clears(lo, hi, NULL);
    mpfr_clear(bound);
    return certified ? 0 : 1;
}
C
  expected=$("$check_dir/pi_window" 1000000 32)
  result=$(./c/bellard_bench segmented 1000000 32 4)
  printf '%s\n' "$result" |
    jq -e --arg expected "$expected" '.certified and .window == $expected'
)
```

### Reproduce timings

Run 3 trials per config and take the median `seconds` (max `rss_bytes` for peak RSS):

```sh
make -C c
./c/euler_grouped 1000000000 32 10
./c/bellard_baseline direct 1000000000 32 10
./c/bellard_baseline grouped 1000000000 32 10
./c/bellard_bench segmented 1000000000 32 10
./c/bellard_bench segmented 10000000000 32 10 256
```

For the Bellard programs, use `CPPFLAGS=-DCOUNT_OPS` or `CPPFLAGS=-DPROFILE_PHASES` with `make -B` for op counts / phase profiling (the Euler/Hutton programs print their counts unconditionally). On AVX-512 IFMA hardware, build `make -C c ifma` and run `./c/euler_grouped_ifma 400000000 32 32` or `./c/euler_grouped_ifma 4000000000 32 32`.

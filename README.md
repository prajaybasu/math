# Computational number theory

The [depth-four Chabauty–Kim certificate](chabauty-kim/README.md) computes both refined components for the thrice-punctured line over $\mathbb Z[1/6]$ at the base-3 Wieferich prime $p=1{,}006{,}003$. It includes the sieve, the root table and reproduction instructions.

## Prime-power grouping for π digit extraction

Extract an arbitrary window of binary or hex digits of $\pi$ without computing the preceding digits. Termwise BBP and Bellard extraction run one modular exponentiation per denominator, $\Theta(n)$ of them; Smith's $(M,3M)$ pairing reduces the constant. Splitting every denominator into prime powers (fractional CRT) and collapsing the $k$-dependent powers of 2 with Euler's criterion leaves one common exponentiation per prime power: $O(n/\log n)$ exponentiations. Total word work is still $O(n \log\log n)$ (sieve and coefficient preparation), in $O(\sqrt{n})$ memory.

Every binary outputs a certified fixed-point enclosure. The `lean/` directory formalizes the finite-sum decomposition and the $O(X / \log X)$ exponentiation bound in Lean 4.

## Benchmarks

Certified 32-bit windows, end-to-end wall time:

| Method | CPU | Bit offset $n$ | Threads | Time | Peak RSS |
| --- | --- | ---: | ---: | ---: | ---: |
| Euler/Hutton grouped (IFMA) | Ryzen 9 9950X | 400,000,000 | 32 | 13.5 ms | 2.5 MB |
| Euler/Hutton grouped (IFMA) | Ryzen 9 9950X | 4,000,000,000 | 32 | 124.5 ms | 2.8 MB |
| Euler/Hutton grouped (scalar) | Apple M4 | 1,000,000,000 | 10 | 0.872 s | 2.11 MiB |
| Smith port, `smith3m` (scalar) | Apple M4 | 1,000,000,000 | 10 | 3.75 s | 1.80 MiB |
| Smith port, `smooth` P=19 (scalar) | Apple M4 | 1,000,000,000 | 10 | 3.08 s | 1.80 MiB |
| Bellard segmented (scalar) | Apple M4 | 1,000,000,000 | 10 | 1.354 s | 2.59 MiB |
| Bellard grouped (unsegmented) | Apple M4 | 1,000,000,000 | 10 | 2.189 s | 1,151.39 MiB |
| Bellard direct | Apple M4 | 1,000,000,000 | 10 | 5.167 s | 1.78 MiB |
| Bellard segmented (scalar) | Apple M4 | 10,000,000,000 | 10 | 14.77 s | 4.08 MiB |

[Robert Smith's IFMA baseline](https://www.stylewarning.com/posts/faster-digit-extraction/#notes-on-a-high-performance-implementation) reported 42.4 ms at 100M hex digits and 410 ms at 1B hex digits (32 threads, width 48, on his machine; not re-run here). At his exact settings (32 threads, 48-bit window at hex positions $10^8$ and $10^9$) the grouped IFMA build takes 13.9 ms and 122 ms on the Ryzen 9 9950X, about 3× faster, but on a different machine, so that comparison is indicative only; the scalar M4 rows are same-machine, same-kernel comparisons with our port of his method. The IFMA build handles $n \lesssim 6.44 \cdot 10^9$ bits (about $1.6 \cdot 10^9$ hex digits); Smith reports runs far beyond that. Full tables and verification scripts are in [docs/benchmarks.md](docs/benchmarks.md).

## Build and run

Requires `make`, a C compiler with `__int128`, and pthreads:

```sh
make -C c
./c/euler_grouped 1000000 32 4
./c/bellard_bench segmented 1000000 32 4
./c/bellard_baseline direct 1000000 32 4
./c/smith_fast smith3m 1000000 19 32 4
./c/smith_fast smooth 1000000 19 32 4
```

On x86-64 with AVX-512 IFMA + DQ:

```sh
make -C c ifma
./c/euler_grouped_ifma 400000000 32 32
```

- `euler_grouped`, `euler_grouped_ifma`: `n [width=32] [threads=1]`
- `bellard_bench`: `direct|grouped|segmented n [width=32] [threads=1] [block_size]` (block size only for `segmented`)
- `bellard_baseline`: `direct|grouped n [width=32] [threads=1]`
- `smith_fast`: `smith3m|smooth n [P=19] [width=32] [threads=1]`; `P` is one of 1, 3, 5, 7, 11, 13, 17, 19, 23 and is ignored by `smith3m`

Width must be 1–64. Thread limits: 16 for `euler_grouped` and `smith_fast`, 10 for the Bellard programs, 128 for IFMA. Invalid arguments exit with status 2.

Bit positions are 1-based (`n=1` is the first bit after the binary point; to skip `h` hex digits and print 12, pass `n=4h+1` and `width=48`). All binaries emit JSON with an MSB-first binary `"window"`, or `"window":null` (exit 1) if the enclosure straddles a boundary.

## Lean 4 proofs

```sh
cd lean && lake exe cache get && lake build
```

`BBPGrouping` proves the Euler-criterion identities for $p \equiv 1, 5 \pmod 8$, the fractional CRT split, finite modular assembly, an explicit $72X / \log X$ bound on the grouped exponentiation count for $X \ge 2$, and the Gaussian prime-divisor elimination core behind $c = \frac{2}{3}$ cutoff optimality in $\mathbb{Q}(i)$. Details in [docs/lean.md](docs/lean.md), [docs/method.md](docs/method.md), and [docs/cutoff-optimality.md](docs/cutoff-optimality.md).

## References

**Author:** Prajay Basu

- [Robert Smith (2026)](https://www.stylewarning.com/posts/faster-digit-extraction/) — $(M, 3M)$ pairing and the Euler/Hutton extraction baseline. The series itself goes back to Euler (1779) and Hutton; Smith's post gives its history and credits.
- [Fabrice Bellard (1997)](https://www.bellard.org/pi/pi_bin/pi_bin.html) & [Bailey–Borwein–Plouffe (1997)](https://www.davidhbailey.com/dhbpapers/digits.pdf) — binary BBP formulas.
- [Quasilinear-Decimal-Extraction](https://github.com/jbabcanec/Quasilinear-Decimal-Extraction) (2026) — already splits extraction sums into prime-power partial fractions, for base-10 digits. This repository applies the idea to binary BBP-type series; what is specific here is the Euler-criterion collapse that gives one common exponent per prime, the segmented low-memory evaluation, the IFMA kernel, and the Lean proofs.
- A. Schinzel, On primitive prime factors of $a^n - b^n$, *Proc. Cambridge Philos. Soc.* 58 (1962) — used in [method.md](docs/method.md#why-the-cutoff-is-2n3-for-this-family).
- J. M. Borwein, D. Borwein, W. F. Galway, Finding and excluding $b$-ary Machin-type individual digit formulae, *Canad. J. Math.* 56 (2004) — the Gaussian-integer and primitive-prime-factor framework behind the cutoff discussion in method.md.

License TBD.

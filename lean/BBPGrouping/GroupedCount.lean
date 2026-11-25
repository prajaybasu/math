module

public import BBPGrouping.BBPSum
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Prime.Int

/-! # Prime-power grouping for finite BBP-type sums

The cost model charges one modular exponentiation per modulus for a common power.
Coefficient arithmetic, factorization, CRT, and integer corrections carry zero charge.
The cutoff counts use natural endpoints and include the endpoint.
-/

public section

namespace BBPGrouping

open Finset Filter

variable {ι : Type*}

/-- One modulus per prime in the common denominator, at its largest input exponent. -/
def maximalPrimePowers (s : Finset ι) (d : ι → ℕ) : Finset ℕ :=
  let L := s.lcm d
  L.primeFactors.image fun p ↦ p ^ L.factorization p

/-- The selected exponent is attained, and no input admits the next power. -/
theorem mem_maximalPrimePowers_iff (s : Finset ι) (d : ι → ℕ) (hd : ∀ i ∈ s, 0 < d i)
    (q : ℕ) :
    q ∈ maximalPrimePowers s d ↔ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ p ^ k = q ∧
      (∃ i ∈ s, p ^ k ∣ d i) ∧ ∀ i ∈ s, ¬p ^ (k + 1) ∣ d i := by
  classical
  have hL := Finset.factorization_lcm (fun i hi ↦ (hd i hi).ne')
  rw [maximalPrimePowers, mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hpp, hdiv, hne⟩ := Nat.mem_primeFactors.mp hp
    have hk := hpp.factorization_pos_of_dvd hne hdiv
    have hs : s.Nonempty := by
      by_contra! he
      simp [he] at hk
    obtain ⟨i, hi, hmax⟩ := s.exists_mem_eq_sup hs (fun j ↦ (d j).factorization p)
    refine ⟨p, _, hpp, hk, rfl, ⟨i, hi, ?_⟩, ?_⟩
    · rw [hpp.pow_dvd_iff_le_factorization (hd i hi).ne', hL, hmax]
    · intro j hj
      rw [hpp.pow_dvd_iff_le_factorization (hd j hj).ne', hL]
      have := le_sup (f := fun t ↦ (d t).factorization p) hj
      omega
  · rintro ⟨p, k, hp, hk, rfl, ⟨i, hi, hki⟩, hnext⟩
    have he : (s.lcm d).factorization p = k := by
      rw [hL]
      apply le_antisymm (Finset.sup_le fun j hj ↦ ?_)
      · exact ((hp.pow_dvd_iff_le_factorization (hd i hi).ne').mp hki).trans
          (le_sup (f := fun j ↦ (d j).factorization p) hi)
      · have := hnext j hj
        rw [hp.pow_dvd_iff_le_factorization (hd j hj).ne'] at this
        omega
    refine ⟨p, ?_, by rw [he]⟩
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, he]
    exact hk.ne'

/-- Iterate the two-factor fractional CRT over pairwise coprime moduli. -/
private theorem crt_over_finset (Q : Finset ℕ) (hpos : ∀ q ∈ Q, 0 < q)
    (hcop : (Q : Set ℕ).Pairwise Nat.Coprime) (A : ℤ) :
    ∃ (c : ℕ → ℤ) (z : ℤ), (A : ℚ) / (Q.prod id : ℕ) = (∑ q ∈ Q, (c q : ℚ) / q) + z := by
  induction Q using Finset.induction_on generalizing A with
  | empty => exact ⟨0, A, by simp⟩
  | @insert q Q hq ih =>
    have hsub := Finset.subset_insert q Q
    have hQ : 0 < Q.prod id := prod_pos fun r hr ↦ hpos r (hsub hr)
    have hqQ : q.Coprime (Q.prod id) :=
      Nat.Coprime.prod_right fun r hr ↦ hcop (mem_insert_self ..) (hsub hr)
        (fun e ↦ hq (e ▸ hr))
    obtain ⟨v, u, w, _, _, hsplit⟩ :=
      crt_fraction_decomposition q (Q.prod id) (hpos q (mem_insert_self ..)) hQ hqQ A
    obtain ⟨c, z, hrest⟩ := ih (fun r hr ↦ hpos r (hsub hr)) (hcop.mono hsub)
      ((A * u) % Q.prod id)
    refine ⟨fun r ↦ if r = q then (A * v) % q else c r, z + w, ?_⟩
    rw [prod_insert hq, Nat.cast_mul, id_eq, hsplit, hrest, sum_insert hq, Int.cast_add]
    have hkeep : ∀ r ∈ Q, r ≠ q := fun r hr e ↦ hq (e ▸ hr)
    simp +contextual [hkeep]
    ring

/-- The finite sum differs by an integer from a sum indexed by exactly the selected moduli.
This holds for all positive denominators, including the positive odd denominators of BBP sums. -/
theorem grouped_assembly (s : Finset ι) (a : ι → ℤ) (d : ι → ℕ) (hd : ∀ i ∈ s, 0 < d i) :
    ∃ (c : ℕ → ℤ) (z : ℤ),
      (∑ i ∈ s, (a i : ℚ) / d i) = (∑ q ∈ maximalPrimePowers s d, (c q : ℚ) / q) + z := by
  let L := s.lcm d
  have hL : L ≠ 0 := lcm_ne_zero_iff.mpr fun i hi ↦ (hd i hi).ne'
  let Q := maximalPrimePowers s d
  have hmem (q : ℕ) : q ∈ Q ↔ ∃ p ∈ L.primeFactors, p ^ L.factorization p = q := mem_image
  have hpos : ∀ q ∈ Q, 0 < q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := (hmem q).mp hq
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hcop : (Q : Set ℕ).Pairwise Nat.Coprime := by
    intro q hq r hr hqr
    obtain ⟨p, hp, rfl⟩ := (hmem _).mp hq
    obtain ⟨t, ht, rfl⟩ := (hmem _).mp hr
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors ht) (fun e ↦ hqr (e ▸ rfl))
  have hprod : Q.prod id = L := by
    change (L.primeFactors.image _).prod id = L
    rw [prod_image]
    · exact (Nat.prod_primeFactors_pow_factorization hL).symm
    · intro p hp t ht eq
      have h (r) (hr : r ∈ L.primeFactors) : L.factorization r ≠ 0 := by
        rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact ((Nat.prime_of_mem_primeFactors hp).pow_inj' (Nat.prime_of_mem_primeFactors ht)
        (h p hp) (h t ht) eq).1
  let A := ∑ i ∈ s, a i * (L / d i : ℕ)
  obtain ⟨c, z, hcrt⟩ := crt_over_finset Q hpos hcop A
  refine ⟨c, z, Eq.trans ?_ hcrt⟩
  rw [hprod, show (A : ℚ) = ∑ i ∈ s, (a i : ℚ) * ((L / d i : ℕ) : ℚ) by
      simp only [A, Int.cast_sum, Int.cast_mul, Int.cast_natCast],
    sum_div]
  apply sum_congr rfl
  intro i hi
  have hmul : (d i : ℚ) * ((L / d i : ℕ) : ℚ) = L := by
    exact_mod_cast Nat.mul_div_cancel' (show d i ∣ L from dvd_lcm hi)
  have hdi : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i hi).ne'
  have hL' : (L : ℚ) ≠ 0 := by exact_mod_cast hL
  field_simp
  linear_combination (a i : ℚ) * hmul.symm

/-- The same coefficients serve for all common powers. Evaluating the grouped side uses
one residue `b ^ e % q` for each `q`. The integer correction disappears modulo one. -/
theorem grouped_modular_assembly (s : Finset ι) (a : ι → ℤ) (d : ι → ℕ)
    (hd : ∀ i ∈ s, 0 < d i) :
    ∃ c : ℕ → ℤ, ∀ (b : ℤ) (e : ℕ), ∃ z : ℤ,
      (∑ i ∈ s, ((b ^ e * a i : ℤ) : ℚ) / d i) =
        (∑ q ∈ maximalPrimePowers s d, (((b ^ e % q) * c q : ℤ) : ℚ) / q) + z := by
  obtain ⟨c, w, h⟩ := grouped_assembly s a d hd
  refine ⟨c, fun b e ↦ ?_⟩
  let m := b ^ e
  let Q := maximalPrimePowers s d
  refine ⟨(∑ q ∈ Q, (m / q) * c q) + m * w, ?_⟩
  have hreduce (q : ℕ) (hq : q ∈ Q) :
      (m : ℚ) * ((c q : ℚ) / q) =
        (((m % q) * c q : ℤ) : ℚ) / q + (((m / q) * c q : ℤ) : ℚ) := by
    have hq' : (q : ℚ) ≠ 0 := by
      obtain ⟨p, k, hp, _, rfl, _⟩ := (mem_maximalPrimePowers_iff s d hd q).mp hq
      exact_mod_cast pow_ne_zero k hp.ne_zero
    have heq : ((m % q : ℤ) : ℚ) + ((m / q : ℤ) : ℚ) * q = m := by
      exact_mod_cast Int.emod_add_ediv_mul m q
    push_cast only [Int.cast_mul]
    field_simp
    linear_combination (c q : ℚ) * heq.symm
  calc
    _ = (m : ℚ) * ∑ i ∈ s, (a i : ℚ) / d i := by
      rw [mul_sum]
      simp only [m, Int.cast_mul, mul_div_assoc]
    _ = (∑ q ∈ Q, (m : ℚ) * ((c q : ℚ) / q)) + (m : ℚ) * w := by
      rw [h, mul_add, mul_sum]
    _ = _ := by
      rw [sum_congr rfl hreduce, sum_add_distrib, Int.cast_add, Int.cast_sum, Int.cast_mul]
      ring

/-- Grouped cutoff budget, charging once for every prime power up to and including `X`. -/
def grouped_cost (X : ℕ) : ℕ := ((Ioc 0 X).filter IsPrimePow).card

/-- Termwise cutoff budget, charging once for every odd denominator up to and including `X`. -/
def termwise_cost (X : ℕ) : ℕ := ((Ioc 0 X).filter Odd).card

/-- Every modulus used by assembly is covered by the grouped cutoff budget. -/
theorem card_maximalPrimePowers_le_grouped_cost (s : Finset ι) (d : ι → ℕ) (X : ℕ)
    (hd : ∀ i ∈ s, 0 < d i) (hX : ∀ i ∈ s, d i ≤ X) :
    (maximalPrimePowers s d).card ≤ grouped_cost X := by
  apply card_le_card
  intro q hq
  obtain ⟨p, k, hp, hk, rfl, ⟨i, hi, hdiv⟩, _⟩ := (mem_maximalPrimePowers_iff s d hd q).mp hq
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨pow_pos hp.pos _, (Nat.le_of_dvd (hd i hi) hdiv).trans
    (hX i hi)⟩, (isPrimePow_nat_iff _).mpr ⟨p, k, hp, hk, rfl⟩⟩

/-- The odd numbers in the cutoff are exactly `2*j+1` for `j < (X+1)/2`. -/
theorem termwise_cost_eq (X : ℕ) : termwise_cost X = (X + 1) / 2 := by
  change ((Ioc 0 X).filter Odd).card = _
  rw [← card_range ((X + 1) / 2)]
  symm
  apply card_bij (fun j _ ↦ 2 * j + 1)
  · intro j hj
    simp only [mem_range] at hj
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ⟨j, rfl⟩⟩
  · intro i hi j hj h
    omega
  · intro q hq
    obtain ⟨hb, j, rfl⟩ := mem_filter.mp hq
    have := (mem_Ioc.mp hb).2
    exact ⟨j, mem_range.mpr (by omega), rfl⟩

open Real
open scoped ArithmeticFunction

/-- Each composite prime power contributes at least `log 2` to Chebyshev's `ψ - θ`. -/
theorem grouped_cost_le_primeCounting_add (X : ℕ) (hX : 2 ≤ X) :
    (grouped_cost X : ℝ) ≤ X.primeCounting + 4 * √(X : ℝ) * log X := by
  let P := (Ioc 0 X).filter IsPrimePow
  let T := P.filter (fun n ↦ ¬n.Prime)
  have hpr : P.filter Nat.Prime = X.primesLE := by
    ext p
    simp only [P, mem_filter, mem_Ioc, Nat.mem_primesLE]
    exact ⟨fun h ↦ ⟨h.1.1.2, h.2⟩, fun ⟨hle, hp⟩ ↦ ⟨⟨⟨hp.pos, hle⟩, hp.isPrimePow⟩, hp⟩⟩
  have hcard : X.primeCounting + T.card = grouped_cost X := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← hpr]
    exact card_filter_add_card_filter_not Nat.Prime
  have hwt : (T.card : ℝ) * log 2 ≤ Chebyshev.psi X - Chebyshev.theta X := calc
    _ = ∑ _n ∈ T, log 2 := by simp
    _ ≤ ∑ n ∈ T, Λ n := by
      apply sum_le_sum
      intro n hn
      obtain ⟨p, k, hp, hk, rfl⟩ :=
        (isPrimePow_nat_iff _).mp (mem_filter.mp (mem_filter.mp hn).1).2
      rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    _ ≤ ∑ n ∈ (Ioc 0 X).filter (fun n ↦ ¬n.Prime), Λ n :=
      sum_le_sum_of_subset_of_nonneg (fun n hn ↦ mem_filter.mpr
        ⟨(mem_filter.mp (mem_filter.mp hn).1).1, (mem_filter.mp hn).2⟩)
        (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := by simp [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  have ht := hwt.trans (Chebyshev.psi_sub_theta_le (by exact_mod_cast (by omega : 1 ≤ X)))
  have htwo : (1 / 2 : ℝ) ≤ log 2 := by
    convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  rw [← hcard, Nat.cast_add]
  linarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg T.card)]

private theorem log_le_two_mul_sqrt (x : ℝ) (hx : 0 ≤ x) : log x ≤ 2 * √x := by
  linarith [log_sqrt hx, log_le_self (sqrt_nonneg x)]

/-- A uniform explicit bound for the grouped modular-exponentiation budget. -/
theorem grouped_cost_le (X : ℕ) (hX : 2 ≤ X) :
    (grouped_cost X : ℝ) ≤ 72 * X / log X := by
  let x : ℝ := X
  have hx : 1 < x := by
    dsimp [x]
    exact_mod_cast (by omega : 1 < X)
  have hx0 : 0 ≤ x := by positivity
  have hl := log_pos hx
  have hπ := Chebyshev.pi_le_log4_mul_div hx
  rw [show ⌊x⌋₊ = X from Nat.floor_natCast X, log_sqrt hx0, div_div_eq_mul_div] at hπ
  have hpow : (grouped_cost X : ℝ) ≤ X.primeCounting + 4 * √x * log x :=
    grouped_cost_le_primeCounting_add X hX
  have hs := log_le_two_mul_sqrt x hx0
  have hss : log x ≤ 4 * √(√x) := by
    linarith [log_sqrt hx0, log_le_two_mul_sqrt (√x) (sqrt_nonneg x)]
  have hs₂ : log x ^ 2 ≤ 16 * √x := by
    have := (sq_le_sq₀ hl.le (by positivity)).mpr hss
    nlinarith [sq_sqrt (sqrt_nonneg x)]
  have hsx : √x * log x ≤ 2 * x := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sqrt_nonneg x), sq_sqrt hx0]
  have hsx₂ : √x * log x ^ 2 ≤ 16 * x := by
    nlinarith [mul_le_mul_of_nonneg_left hs₂ (sqrt_nonneg x), sq_sqrt hx0]
  change (grouped_cost X : ℝ) ≤ 72 * x / log x
  rw [le_div_iff₀ hl]
  have hπ' := mul_le_mul_of_nonneg_right hπ hl.le
  rw [add_mul, div_mul_cancel₀ _ hl.ne'] at hπ'
  nlinarith [mul_le_mul_of_nonneg_right hpow hl.le,
    mul_le_mul_of_nonneg_right (log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)) hx0]

/-- The fraction of the termwise modular-exponentiation budget charged by grouping tends to zero. -/
theorem grouped_cost_div_termwise_cost_tendsto_zero :
    Tendsto (fun X : ℕ ↦ (grouped_cost X : ℝ) / termwise_cost X) atTop (nhds 0) := by
  have hlim : Tendsto (fun X : ℕ ↦ 144 / log (X : ℝ)) atTop (nhds 0) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop 144
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _ hlim
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hhalf : X ≤ 2 * termwise_cost X := by
    rw [termwise_cost_eq]
    omega
  have ht : 0 < (termwise_cost X : ℝ) := by exact_mod_cast (by omega : 0 < termwise_cost X)
  have hl : 0 < log (X : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < X))
  have h := (le_div_iff₀ hl).mp (grouped_cost_le X hX)
  rw [div_le_div_iff₀ ht hl]
  have hhalf' : (X : ℝ) ≤ 2 * termwise_cost X := by exact_mod_cast hhalf
  linarith

/-- Specialization to the actual moduli used when all odd denominators up to `X` occur. -/
theorem odd_cutoff_moduli_ratio_tendsto_zero :
    Tendsto (fun X : ℕ ↦ ((maximalPrimePowers ((Ioc 0 X).filter Odd) id).card : ℝ) /
      termwise_cost X) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) _
    grouped_cost_div_termwise_cost_tendsto_zero
  apply Eventually.of_forall
  intro X
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_maximalPrimePowers_le_grouped_cost ((Ioc 0 X).filter Odd) id X
    (fun i hi ↦ (mem_Ioc.mp (mem_filter.mp hi).1).1)
    (fun i hi ↦ (mem_Ioc.mp (mem_filter.mp hi).1).2)

end BBPGrouping

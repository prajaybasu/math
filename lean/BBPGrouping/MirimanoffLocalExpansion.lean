module

public import BBPGrouping.MirimanoffSieve
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Local `p`-adic expansion congruences `hY1–hY4` for `mirimanoff_sieve_sound`

We derive the four mod-`p` congruences `hY1–hY4` assumed by
`BBPGrouping.mirimanoff_sieve_sound` directly from the Coleman local power-series
expansion of `Y_m(L) = p^(-m) Li_m(ζ_a e^(pL))` in `L = log_p(z) / p ∈ ℤ_[p]`
for primes `p ≥ 7` and weights `m ∈ {1, 2, 3, 4}`:

  `Y_m(L) = ∑_{j=0}^{m-1} (c_{m-j} / j!) L^j + (b_0 / m!) L^m + tail_m(L)`,

where

  `tail_m(L) = ∑' k : ℕ, b (k + 1) * (p : ℚ_[p])^(k+1) / ((k+1+m)! : ℚ_[p]) * L^(k+1+m)`.

Key results:
1. `factorial_multiplicity_le_half`: for prime `p ≥ 7`, `m ≤ 4`, `k ≥ 1`,
   `multiplicity p (k + m)! ≤ k / 2` (and `multiplicity p (k + m)! + 1 ≤ k`).
2. `local_tail_term_norm_le_inv_p`: every tail term has `p`-adic norm `≤ p⁻¹` uniformly
   for all `L : ℤ_[p]`.
3. `local_tail_summable`: the tail series is uniformly summable in `ℚ_[p]` for all `L : ℤ_[p]`.
4. `local_tail_norm_le_inv_p`: by the ultrametric inequality, `‖tail_m(L)‖ ≤ p⁻¹` uniformly
   for all `L : ℤ_[p]`, so `tail_m(L) ∈ ℤ_[p]` and `PadicInt.toZMod tail_m(L) = 0`.
5. `local_expansion_toZMod_Y1`..`Y4` and `mirimanoff_sieve_from_local_expansion`:
   derives `hY1–hY4` from the Coleman local expansion (stated explicitly as a hypothesis)
   and combines them with `mirimanoff_sieve_sound`.
-/

public section

namespace BBPGrouping

/-- The `k`-th tail term (`k` shifted by `+1`) of the weight-`m` local expansion in `ℚ_[p]`. -/
noncomputable def localTailTerm (p m : ℕ) [Fact p.Prime] (b : ℕ → ℤ_[p]) (L : ℤ_[p]) (k : ℕ) :
    ℚ_[p] :=
  (b (k + 1) : ℚ_[p]) * ((p : ℚ_[p]) ^ (k + 1) / (((k + 1 + m).factorial : ℕ) : ℚ_[p])) *
    (L : ℚ_[p]) ^ (k + 1 + m)

/-- The infinite tail `∑' k, localTailTerm p m b L k` in `ℚ_[p]`. -/
noncomputable def localTail (p m : ℕ) [Fact p.Prime] (b : ℕ → ℤ_[p]) (L : ℤ_[p]) : ℚ_[p] :=
  ∑' k : ℕ, localTailTerm p m b L k

/-- Legendre's bound for prime `p ≥ 7`, weight `m ≤ 4`, and `k ≥ 1`:
`multiplicity p (k + m)! ≤ k / 2`. -/
theorem factorial_multiplicity_le_half (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (m k : ℕ) (hm : m ≤ 4) (hk : 1 ≤ k) :
    multiplicity p (k + m).factorial ≤ k / 2 := by
  have hlt := sub_one_mul_multiplicity_factorial_lt_of_ne_zero p (n := k + m) (by omega)
  have h6 : 6 * multiplicity p (k + m).factorial < k + m :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega : 6 ≤ p - 1)) hlt
  omega

/-- Consequence of `factorial_multiplicity_le_half`: `multiplicity p (k + m)! + 1 ≤ k`
for all prime `p ≥ 7`, `m ≤ 4`, `k ≥ 1`. -/
theorem factorial_multiplicity_lt (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (m k : ℕ) (hm : m ≤ 4) (hk : 1 ≤ k) :
    multiplicity p (k + m).factorial + 1 ≤ k := by
  have h := factorial_multiplicity_le_half p hp7 m k hm hk
  omega

private theorem norm_p_pow_div_factorial (p m k : ℕ) [Fact p.Prime] :
    ‖(p : ℚ_[p]) ^ (k + 1) / (((k + 1 + m).factorial : ℕ) : ℚ_[p])‖ =
      (p : ℝ) ^ ((multiplicity p (k + 1 + m).factorial : ℤ) - ((k + 1 : ℕ) : ℤ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfac_ne : (((k + 1 + m).factorial : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hfac_ne,
    Padic.valuation_natCast, ← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_sub₀ hp_pos.ne']
  ring_nf

/-- Exponential decay of each tail term, uniform over all `L : ℤ_[p]`:
`‖localTailTerm p m b L k‖ ≤ ((p : ℝ)⁻¹) ^ ((k + 2) / 2)`. -/
theorem local_tail_term_norm_le_pow (p m : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hm : m ≤ 4) (b : ℕ → ℤ_[p]) (L : ℤ_[p]) (k : ℕ) :
    ‖localTailTerm p m b L k‖ ≤ ((p : ℝ)⁻¹) ^ ((k + 2) / 2) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hb : ‖(b (k + 1) : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (b (k + 1))
  have hL : ‖(L : ℚ_[p]) ^ (k + 1 + m)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one L)
  have hval := factorial_multiplicity_le_half p hp7 m (k + 1) hm (by omega)
  have hexp : (multiplicity p (k + 1 + m).factorial : ℤ) - ((k + 1 : ℕ) : ℤ) ≤
      -(((k + 2) / 2 : ℕ) : ℤ) := by omega
  calc ‖localTailTerm p m b L k‖
      = ‖(b (k + 1) : ℚ_[p])‖ *
          ‖(p : ℚ_[p]) ^ (k + 1) / (((k + 1 + m).factorial : ℕ) : ℚ_[p])‖ *
          ‖(L : ℚ_[p]) ^ (k + 1 + m)‖ := by
        simp only [localTailTerm, norm_mul]
    _ ≤ 1 * ‖(p : ℚ_[p]) ^ (k + 1) / (((k + 1 + m).factorial : ℕ) : ℚ_[p])‖ * 1 := by
        gcongr
    _ = (p : ℝ) ^ ((multiplicity p (k + 1 + m).factorial : ℤ) - ((k + 1 : ℕ) : ℤ)) := by
        rw [one_mul, mul_one, norm_p_pow_div_factorial]
    _ ≤ (p : ℝ) ^ (-(((k + 2) / 2 : ℕ) : ℤ)) := zpow_le_zpow_right₀ hp1 hexp
    _ = ((p : ℝ)⁻¹) ^ ((k + 2) / 2) := by rw [zpow_neg, zpow_natCast, inv_pow]

/-- Uniform bound `‖localTailTerm p m b L k‖ ≤ p⁻¹` for every `k : ℕ` and every `L : ℤ_[p]`. -/
theorem local_tail_term_norm_le_inv_p (p m : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hm : m ≤ 4) (b : ℕ → ℤ_[p]) (L : ℤ_[p]) (k : ℕ) :
    ‖localTailTerm p m b L k‖ ≤ (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hinv_le1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hinv_nn : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpow : ((p : ℝ)⁻¹) ^ ((k + 2) / 2) ≤ ((p : ℝ)⁻¹) ^ 1 :=
    pow_le_pow_of_le_one hinv_nn hinv_le1 (by omega : 1 ≤ (k + 2) / 2)
  simpa using (local_tail_term_norm_le_pow p m hp7 hm b L k).trans hpow

/-- Uniform summability of the local tail series in `ℚ_[p]` for all `L : ℤ_[p]`. -/
theorem local_tail_summable (p m : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hm : m ≤ 4) (b : ℕ → ℤ_[p]) (L : ℤ_[p]) :
    Summable (localTailTerm p m b L) := by
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr_nn : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hr_lt1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
  have hsqrt_lt1 : Real.sqrt (p : ℝ)⁻¹ < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hr_nn hr_lt1
  have hsqrt_nn : 0 ≤ Real.sqrt (p : ℝ)⁻¹ := Real.sqrt_nonneg _
  have hgeom : Summable (fun k : ℕ => (Real.sqrt (p : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one hsqrt_nn hsqrt_lt1
  refine Summable.of_norm_bounded hgeom fun k => ?_
  have hle := local_tail_term_norm_le_pow p m hp7 hm b L k
  have hpow_le : ((p : ℝ)⁻¹) ^ ((k + 2) / 2) ≤ (Real.sqrt (p : ℝ)⁻¹) ^ k := by
    calc ((p : ℝ)⁻¹) ^ ((k + 2) / 2)
        = ((Real.sqrt (p : ℝ)⁻¹) ^ 2) ^ ((k + 2) / 2) := by rw [Real.sq_sqrt hr_nn]
      _ = (Real.sqrt (p : ℝ)⁻¹) ^ (2 * ((k + 2) / 2)) := by rw [← pow_mul]
      _ ≤ (Real.sqrt (p : ℝ)⁻¹) ^ k :=
          pow_le_pow_of_le_one hsqrt_nn hsqrt_lt1.le (by omega)
  exact hle.trans hpow_le

private theorem padic_norm_finset_sum_le {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ_[p]) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i ∈ s, ‖f i‖ ≤ c) :
    ‖∑ i ∈ s, f i‖ ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have htri : ‖f a + ∑ i ∈ s, f i‖ ≤ max ‖f a‖ ‖∑ i ∈ s, f i‖ := by
      have h := dist_triangle_max (f a) 0 (-(∑ i ∈ s, f i))
      simpa [dist_eq_norm] using h
    exact htri.trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **Uniform ultrametric tail bound:** `‖localTail p m b L‖ ≤ p⁻¹` for all `L : ℤ_[p]`. -/
theorem local_tail_norm_le_inv_p (p m : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hm : m ≤ 4) (b : ℕ → ℤ_[p]) (L : ℤ_[p]) :
    ‖localTail p m b L‖ ≤ (p : ℝ)⁻¹ := by
  have hsum := (local_tail_summable p m hp7 hm b L).hasSum
  have htend : Filter.Tendsto (fun n : ℕ => ‖∑ k ∈ Finset.range n, localTailTerm p m b L k‖)
      Filter.atTop (nhds ‖localTail p m b L‖) :=
    (continuous_norm.tendsto _).comp hsum.tendsto_sum_nat
  refine le_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
  exact padic_norm_finset_sum_le (Finset.range n) (localTailTerm p m b L)
    (inv_nonneg.mpr (by positivity))
    (fun k _ => local_tail_term_norm_le_inv_p p m hp7 hm b L k)

/-- The tail lies in `ℤ_[p]` and vanishes modulo `p`, uniformly for all `L : ℤ_[p]`. -/
theorem local_tail_toZMod_eq_zero (p m : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hm : m ≤ 4) (b : ℕ → ℤ_[p]) (L : ℤ_[p]) (tail : ℤ_[p])
    (htail : (tail : ℚ_[p]) = localTail p m b L) :
    PadicInt.toZMod tail = 0 := by
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlt1 : ‖tail‖ < 1 := by
    change ‖(tail : ℚ_[p])‖ < 1
    rw [htail]
    exact (local_tail_norm_le_inv_p p m hp7 hm b L).trans_lt (inv_lt_one_of_one_lt₀ hp_gt1)
  have hdvd : (p : ℤ_[p]) ∣ tail := (PadicInt.norm_lt_one_iff_dvd tail).mp hlt1
  obtain ⟨y, hy⟩ := hdvd
  rw [hy, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem padicInt_of_norm_le_inv_p_toZMod {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (hx : ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹) : PadicInt.toZMod x = 0 := by
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlt1 : ‖x‖ < 1 := hx.trans_lt (inv_lt_one_of_one_lt₀ hp_gt1)
  obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hlt1
  rw [hy, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem zmod_natCast_ne_zero_of_lt {p : ℕ} [Fact p.Prime] (n : ℕ)
    (hn0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h
  have hle : p ≤ n := Nat.le_of_dvd hn0 hdvd
  omega

/-- Congruence `hY1` derived from the weight-1 local expansion in `L : ℤ_[p]`. -/
theorem local_expansion_toZMod_Y1 (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (a c1 : ZMod p) (b : ℕ → ℤ_[p]) (c1_lift L Y1 : ℤ_[p])
    (hb0 : PadicInt.toZMod (b 0) = a * (1 - a)⁻¹)
    (hc1 : PadicInt.toZMod c1_lift = c1)
    (hY1_exp : (Y1 : ℚ_[p]) = (c1_lift : ℚ_[p]) + (b 0 : ℚ_[p]) * (L : ℚ_[p]) +
      localTail p 1 b L) :
    PadicInt.toZMod Y1 = c1 + (a * (1 - a)⁻¹) * PadicInt.toZMod L := by
  have hdiff : ((Y1 - (c1_lift + b 0 * L) : ℤ_[p]) : ℚ_[p]) = localTail p 1 b L := by
    push_cast
    linear_combination hY1_exp
  have h0 : PadicInt.toZMod (Y1 - (c1_lift + b 0 * L)) = 0 :=
    local_tail_toZMod_eq_zero p 1 hp7 (by omega) b L _ hdiff
  rw [map_sub, map_add, map_mul, hc1, hb0, sub_eq_zero] at h0
  exact h0

/-- Congruence `hY2` derived from the weight-2 local expansion in `L : ℤ_[p]`. -/
theorem local_expansion_toZMod_Y2 (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (a c1 c2 : ZMod p) (b : ℕ → ℤ_[p]) (c1_lift c2_lift L Y2 : ℤ_[p])
    (hb0 : PadicInt.toZMod (b 0) = a * (1 - a)⁻¹)
    (hc1 : PadicInt.toZMod c1_lift = c1)
    (hc2 : PadicInt.toZMod c2_lift = c2)
    (hY2_exp : (Y2 : ℚ_[p]) = (c2_lift : ℚ_[p]) + (c1_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (b 0 : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + localTail p 2 b L) :
    PadicInt.toZMod Y2 =
      c2 + c1 * PadicInt.toZMod L + (a * (1 - a)⁻¹) * (2 : ZMod p)⁻¹ * (PadicInt.toZMod L) ^ 2 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    simpa using zmod_natCast_ne_zero_of_lt (p := p) 2 (by omega) (by omega)
  have hdiff :
      (((2 : ℤ_[p]) * Y2 - (2 * c2_lift + 2 * c1_lift * L + b 0 * L ^ 2) : ℤ_[p]) : ℚ_[p]) =
      2 * localTail p 2 b L := by
    have h2c : ((2 : ℤ_[p]) : ℚ_[p]) = 2 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    simp only [PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, h2c]
    linear_combination 2 * hY2_exp
  have hnorm :
      ‖(((2 : ℤ_[p]) * Y2 - (2 * c2_lift + 2 * c1_lift * L + b 0 * L ^ 2) : ℤ_[p]) : ℚ_[p])‖ ≤
      (p : ℝ)⁻¹ := by
    rw [hdiff, norm_mul]
    have h2 : ‖(2 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast PadicInt.norm_le_one (2 : ℤ_[p])
    calc ‖(2 : ℚ_[p])‖ * ‖localTail p 2 b L‖
        ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul h2 (local_tail_norm_le_inv_p p 2 hp7 (by omega) b L)
          (norm_nonneg _) (by norm_num)
      _ = (p : ℝ)⁻¹ := one_mul _
  have h0 := padicInt_of_norm_le_inv_p_toZMod hnorm
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hc1, hc2, hb0, sub_eq_zero] at h0
  field_simp [h2ne]
  linear_combination h0

/-- Congruence `hY3` derived from the weight-3 local expansion in `L : ℤ_[p]`. -/
theorem local_expansion_toZMod_Y3 (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (c3 : ZMod p) (b : ℕ → ℤ_[p]) (c1_lift c2_lift c3_lift L Y3 : ℤ_[p])
    (hc3 : PadicInt.toZMod c3_lift = c3)
    (hY3_exp : (Y3 : ℚ_[p]) = (c3_lift : ℚ_[p]) + (c2_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (c1_lift : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + (b 0 : ℚ_[p]) / 6 * (L : ℚ_[p]) ^ 3 +
      localTail p 3 b L)
    (hL0 : PadicInt.toZMod L = 0) :
    PadicInt.toZMod Y3 = c3 := by
  have h6ne : (6 : ZMod p) ≠ 0 := by
    simpa using zmod_natCast_ne_zero_of_lt (p := p) 6 (by omega) (by omega)
  have hdiff : (((6 : ℤ_[p]) * Y3 -
      (6 * c3_lift + 6 * c2_lift * L + 3 * c1_lift * L ^ 2 + b 0 * L ^ 3) : ℤ_[p]) : ℚ_[p]) =
      6 * localTail p 3 b L := by
    have h6c : ((6 : ℤ_[p]) : ℚ_[p]) = 6 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    have h3c : ((3 : ℤ_[p]) : ℚ_[p]) = 3 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    simp only [PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, h6c, h3c]
    linear_combination 6 * hY3_exp
  have hnorm : ‖(((6 : ℤ_[p]) * Y3 -
      (6 * c3_lift + 6 * c2_lift * L + 3 * c1_lift * L ^ 2 + b 0 * L ^ 3) : ℤ_[p]) : ℚ_[p])‖ ≤
      (p : ℝ)⁻¹ := by
    rw [hdiff, norm_mul]
    have h6 : ‖(6 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast PadicInt.norm_le_one (6 : ℤ_[p])
    calc ‖(6 : ℚ_[p])‖ * ‖localTail p 3 b L‖
        ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul h6 (local_tail_norm_le_inv_p p 3 hp7 (by omega) b L)
          (norm_nonneg _) (by norm_num)
      _ = (p : ℝ)⁻¹ := one_mul _
  have h0 := padicInt_of_norm_le_inv_p_toZMod hnorm
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hc3, hL0, mul_zero, zero_pow,
    add_zero, sub_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h0
  exact mul_left_cancel₀ h6ne h0

/-- Congruence `hY4` derived from the weight-4 local expansion in `L : ℤ_[p]`. -/
theorem local_expansion_toZMod_Y4 (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (c4 : ZMod p) (b : ℕ → ℤ_[p]) (c1_lift c2_lift c3_lift c4_lift L Y4 : ℤ_[p])
    (hc4 : PadicInt.toZMod c4_lift = c4)
    (hY4_exp : (Y4 : ℚ_[p]) = (c4_lift : ℚ_[p]) + (c3_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (c2_lift : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + (c1_lift : ℚ_[p]) / 6 * (L : ℚ_[p]) ^ 3 +
      (b 0 : ℚ_[p]) / 24 * (L : ℚ_[p]) ^ 4 + localTail p 4 b L)
    (hL0 : PadicInt.toZMod L = 0) :
    PadicInt.toZMod Y4 = c4 := by
  have h24ne : (24 : ZMod p) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := by
      simpa using zmod_natCast_ne_zero_of_lt (p := p) 2 (by omega) (by omega)
    have h3 : (3 : ZMod p) ≠ 0 := by
      simpa using zmod_natCast_ne_zero_of_lt (p := p) 3 (by omega) (by omega)
    have : (24 : ZMod p) = 2 * 2 * 2 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3
  have hdiff : (((24 : ℤ_[p]) * Y4 -
      (24 * c4_lift + 24 * c3_lift * L + 12 * c2_lift * L ^ 2 +
        4 * c1_lift * L ^ 3 + b 0 * L ^ 4) : ℤ_[p]) : ℚ_[p]) =
      24 * localTail p 4 b L := by
    have h24c : ((24 : ℤ_[p]) : ℚ_[p]) = 24 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    have h12c : ((12 : ℤ_[p]) : ℚ_[p]) = 12 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    have h4c : ((4 : ℤ_[p]) : ℚ_[p]) = 4 := by
      rw [← Nat.cast_ofNat (R := ℤ_[p]), PadicInt.coe_natCast, Nat.cast_ofNat]
    simp only [PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      h24c, h12c, h4c]
    linear_combination 24 * hY4_exp
  have hnorm : ‖(((24 : ℤ_[p]) * Y4 -
      (24 * c4_lift + 24 * c3_lift * L + 12 * c2_lift * L ^ 2 +
        4 * c1_lift * L ^ 3 + b 0 * L ^ 4) : ℤ_[p]) : ℚ_[p])‖ ≤
      (p : ℝ)⁻¹ := by
    rw [hdiff, norm_mul]
    have h24 : ‖(24 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast PadicInt.norm_le_one (24 : ℤ_[p])
    calc ‖(24 : ℚ_[p])‖ * ‖localTail p 4 b L‖
        ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul h24 (local_tail_norm_le_inv_p p 4 hp7 (by omega) b L)
          (norm_nonneg _) (by norm_num)
      _ = (p : ℝ)⁻¹ := one_mul _
  have h0 := padicInt_of_norm_le_inv_p_toZMod hnorm
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hc4, hL0, mul_zero, zero_pow,
    add_zero, sub_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at h0
  exact mul_left_cancel₀ h24ne h0

/-- **End-to-end Mirimanoff depth-4 sieve theorem from Coleman local expansions:**
For any prime `p ≥ 7`, given the Coleman local expansions of `Y1..Y4` in `L = log_p(z) / p ∈ ℤ_[p]`
(literature hypothesis: Besser–de Jeu / Lüdtke), every common `p`-adic root of the two depth-4
Chabauty–Kim functions survives the finite-field sieve. -/
theorem mirimanoff_sieve_from_local_expansion (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (a c1 c2 c3 c4 : ZMod p) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (b : ℕ → ℤ_[p]) (c1_lift c2_lift c3_lift c4_lift : ℤ_[p])
    (hb0 : PadicInt.toZMod (b 0) = a * (1 - a)⁻¹)
    (hc1 : PadicInt.toZMod c1_lift = c1) (hc2 : PadicInt.toZMod c2_lift = c2)
    (hc3 : PadicInt.toZMod c3_lift = c3) (hc4 : PadicInt.toZMod c4_lift = c4)
    (l2 l3 c23 A B C L Y1 Y2 Y3 Y4 : ℤ_[p])
    (hl2 : PadicInt.toZMod l2 ≠ 0) (hl3 : PadicInt.toZMod l3 ≠ 0)
    (hc23 : PadicInt.toZMod c23 ≠ 0) (hC : PadicInt.toZMod C ≠ 0)
    (hY1_exp : (Y1 : ℚ_[p]) = (c1_lift : ℚ_[p]) + (b 0 : ℚ_[p]) * (L : ℚ_[p]) +
      localTail p 1 b L)
    (hY2_exp : (Y2 : ℚ_[p]) = (c2_lift : ℚ_[p]) + (c1_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (b 0 : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + localTail p 2 b L)
    (hY3_exp : (Y3 : ℚ_[p]) = (c3_lift : ℚ_[p]) + (c2_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (c1_lift : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + (b 0 : ℚ_[p]) / 6 * (L : ℚ_[p]) ^ 3 +
      localTail p 3 b L)
    (hY4_exp : (Y4 : ℚ_[p]) = (c4_lift : ℚ_[p]) + (c3_lift : ℚ_[p]) * (L : ℚ_[p]) +
      (c2_lift : ℚ_[p]) / 2 * (L : ℚ_[p]) ^ 2 + (c1_lift : ℚ_[p]) / 6 * (L : ℚ_[p]) ^ 3 +
      (b 0 : ℚ_[p]) / 24 * (L : ℚ_[p]) ^ 4 + localTail p 4 b L)
    (hf2 : (p : ℤ_[p]) ^ 5 * l2 * l3 * Y2 + (p : ℤ_[p]) ^ 4 * c23 * L * Y1 = 0)
    (hf4 : (p : ℤ_[p]) ^ 16 * A * Y4 + (p : ℤ_[p]) ^ 15 * B * L * Y3 +
      (p : ℤ_[p]) ^ 13 * C * L ^ 3 * Y1 = 0) :
    (c1 = 0 ∧ c2 = 0) ∨
    (c1 ≠ 0 ∧
      let u := -(PadicInt.toZMod l2 * PadicInt.toZMod l3 * (PadicInt.toZMod c23)⁻¹) * c2 * c1⁻¹
      PadicInt.toZMod A * c4 + PadicInt.toZMod B * u * c3 +
        PadicInt.toZMod C * u ^ 3 * c1 = 0) ∨
    (c1 ≠ 0 ∧ 2 * c2 * a - c1 ^ 2 * (1 - a) = 0) :=
  mirimanoff_sieve_sound p (by omega) a c1 c2 c3 c4 ha0 ha1 l2 l3 c23 A B C L Y1 Y2 Y3 Y4
    hl2 hl3 hc23 hC
    (local_expansion_toZMod_Y1 p hp7 a c1 b c1_lift L Y1 hb0 hc1 hY1_exp)
    (local_expansion_toZMod_Y2 p hp7 a c1 c2 b c1_lift c2_lift L Y2 hb0 hc1 hc2 hY2_exp)
    (local_expansion_toZMod_Y3 p hp7 c3 b c1_lift c2_lift c3_lift L Y3 hc3 hY3_exp)
    (local_expansion_toZMod_Y4 p hp7 c4 b c1_lift c2_lift c3_lift c4_lift L Y4 hc4 hY4_exp)
    hf2 hf4

end BBPGrouping

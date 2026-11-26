module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Common lifting criterion modulo `p^(n+1)` from modulo `p^n` (`n ≥ 1`)

For two normalized integral local equations `F(x) = 0`, `G(x) = 0` over `ℤ_[p]`
vanishing modulo `p^n` at `x` (`F x = p^n * cF`, `G x = p^n * cG`) with
first-order Taylor expansions modulo `p^(n+1)`:
  `F (x + p^n * u) ≡ F x + p^n * dF * u (mod p^(n+1))`
  `G (x + p^n * u) ≡ G x + p^n * dG * u (mod p^(n+1))`,
we prove the exact necessary-and-sufficient criterion for the existence of a common
digit `u : ℤ_[p]` making both vanish at `x + p^n * u` modulo `p^(n+1)`, including
the doubly singular case where both reduced derivatives vanish (`π(dF) = 0 ∧ π(dG) = 0`):

  `(∃ u : ℤ_[p], (p : ℤ_[p])^(n+1) ∣ F (x + p^n * u) ∧ (p : ℤ_[p])^(n+1) ∣ G (x + p^n * u))`
  `↔ π(cF) * π(dG) = π(cG) * π(dF) ∧ ((π(dF) = 0 ∧ π(dG) = 0) → (π(cF) = 0 ∧ π(cG) = 0))`.

We also prove:
- `no_common_lift_of_obstruction_det_ne_zero`: a nonzero obstruction determinant
  `π(cF) * π(dG) - π(cG) * π(dF) ≠ 0` excludes every lift `x + p^n * u` modulo `p^(n+1)`.
- `common_lift_digit_unique`: uniqueness of the digit `π(u)` whenever at least one
  reduced derivative is nonzero.
- `common_lift_all_of_doubly_singular`: every `u : ℤ_[p]` lifts when both derivatives
  and both normalized residues vanish modulo `p`.
- `common_lift_invariant`: invariance of the criterion under shifting `x ↦ x + p^n * s`.
- `poly_common_mod_p_pow_succ_lift_iff` and `poly_no_common_lift_of_obstruction_det_ne_zero`:
  automatic specializations to polynomial equations `F, G : Polynomial ℤ_[p]` for `n ≥ 1`.
- `common_mod_p_sq_lift_iff` and `poly_common_mod_p_sq_lift_iff`: the `n = 1` (`p → p^2`)
  specializations.
-/

public section

namespace BBPGrouping.CommonSecondDigit

open Polynomial

private theorem padicInt_p_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℤ_[p]) ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  exact_mod_cast hp

private theorem padicInt_dvd_of_toZMod_eq_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (hx : PadicInt.toZMod x = 0) : ∃ y : ℤ_[p], x = (p : ℤ_[p]) * y := by
  have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hx
  have hnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hmem
  have hnorm : ‖x‖ < 1 :=
    lt_of_le_of_ne (PadicInt.norm_le_one x) (fun h1 => hnu (PadicInt.isUnit_iff.mpr h1))
  exact (PadicInt.norm_lt_one_iff_dvd x).mp hnorm

private theorem padicInt_p_pow_succ_dvd_p_pow_mul_iff {p : ℕ} [Fact p.Prime] (n : ℕ) (x : ℤ_[p]) :
    (p : ℤ_[p]) ^ (n + 1) ∣ (p : ℤ_[p]) ^ n * x ↔ PadicInt.toZMod x = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    have hx : x = (p : ℤ_[p]) * q := by
      apply mul_left_cancel₀ (pow_ne_zero n (padicInt_p_ne_zero p))
      simpa only [pow_succ, mul_assoc] using hq
    rw [hx, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  · intro hx
    obtain ⟨y, hy⟩ := padicInt_dvd_of_toZMod_eq_zero hx
    refine ⟨y, ?_⟩
    rw [hy, pow_succ, mul_assoc]

private theorem exists_padicInt_toZMod_eq {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    ∃ t : ℤ_[p], PadicInt.toZMod t = a := by
  refine ⟨(a.val : ℤ_[p]), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- Field-level necessary-and-sufficient criterion for two linear equations
`cF + dF * u = 0` and `cG + dG * u = 0` over any field `K` to admit a common root `u`,
including the doubly singular case `dF = 0 ∧ dG = 0`. -/
theorem field_common_linear_root_iff {K : Type*} [Field K] (cF dF cG dG : K) :
    (∃ u : K, cF + dF * u = 0 ∧ cG + dG * u = 0) ↔
      cF * dG = cG * dF ∧ ((dF = 0 ∧ dG = 0) → (cF = 0 ∧ cG = 0)) := by
  constructor
  · rintro ⟨u, hF, hG⟩
    refine ⟨?_, ?_⟩
    · have h1 : cF * dG = -(dF * u) * dG := by linear_combination dG * hF
      have h2 : cG * dF = -(dG * u) * dF := by linear_combination dF * hG
      rw [h1, h2]
      ring
    · rintro ⟨hdF, hdG⟩
      simp only [hdF, hdG, zero_mul, add_zero] at hF hG
      exact ⟨hF, hG⟩
  · rintro ⟨hdet, hsing⟩
    by_cases hdF : dF ≠ 0
    · refine ⟨-cF / dF, ?_, ?_⟩
      · field_simp [hdF]
        ring
      · field_simp [hdF]
        linear_combination -hdet
    · push Not at hdF
      by_cases hdG : dG ≠ 0
      · refine ⟨-cG / dG, ?_, ?_⟩
        · have hcF : cF = 0 := by
            have h0 : cF * dG = 0 := by simpa [hdF] using hdet
            exact (mul_eq_zero.mp h0).resolve_right hdG
          simp [hdF, hcF]
        · field_simp [hdG]
          ring
      · push Not at hdG
        obtain ⟨hcF, hcG⟩ := hsing ⟨hdF, hdG⟩
        exact ⟨0, by simp [hdF, hcF], by simp [hdG, hcG]⟩

/-- Equivalent branch-disjunction form of `field_common_linear_root_iff`. -/
theorem field_common_linear_root_iff_branches {K : Type*} [Field K] (cF dF cG dG : K) :
    (∃ u : K, cF + dF * u = 0 ∧ cG + dG * u = 0) ↔
      ((dF ≠ 0 ∨ dG ≠ 0) ∧ cF * dG = cG * dF) ∨
        (dF = 0 ∧ dG = 0 ∧ cF = 0 ∧ cG = 0) := by
  rw [field_common_linear_root_iff]
  by_cases h : dF = 0 ∧ dG = 0
  · rcases h with ⟨hdF, hdG⟩
    simp [hdF, hdG]
  · constructor
    · rintro ⟨hdet, _⟩
      left
      refine ⟨?_, hdet⟩
      by_contra hne
      push Not at hne
      exact h hne
    · rintro (⟨_, hdet⟩ | ⟨hdF, hdG, _⟩)
      · exact ⟨hdet, fun h0 => (h h0).elim⟩
      · exact (h ⟨hdF, hdG⟩).elim

/-- Whenever at least one derivative is nonzero, any common solution `u` is unique. -/
theorem field_common_linear_root_unique {K : Type*} [Field K] {cF dF cG dG u₁ u₂ : K}
    (hnd : dF ≠ 0 ∨ dG ≠ 0)
    (h₁ : cF + dF * u₁ = 0 ∧ cG + dG * u₁ = 0)
    (h₂ : cF + dF * u₂ = 0 ∧ cG + dG * u₂ = 0) : u₁ = u₂ := by
  rcases hnd with hdF | hdG
  · have hsub : dF * (u₁ - u₂) = 0 := by linear_combination h₁.1 - h₂.1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hdF)
  · have hsub : dG * (u₁ - u₂) = 0 := by linear_combination h₁.2 - h₂.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left hdG)

/-- Single-equation lifting step from modulo `p^n` to modulo `p^(n+1)`. -/
theorem mod_p_pow_succ_lift_single_iff {p : ℕ} [Fact p.Prime] (n : ℕ)
    (F : ℤ_[p] → ℤ_[p]) (x c d u : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) ^ n * c)
    (hF_taylor : ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) ^ n * u) =
        F x + (p : ℤ_[p]) ^ n * d * u + (p : ℤ_[p]) ^ (n + 1) * r) :
    (p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u) ↔
      PadicInt.toZMod c + PadicInt.toZMod d * PadicInt.toZMod u = 0 := by
  obtain ⟨r, hr⟩ := hF_taylor
  have hrew : F (x + (p : ℤ_[p]) ^ n * u) =
      (p : ℤ_[p]) ^ n * (c + d * u) + (p : ℤ_[p]) ^ (n + 1) * r := by
    rw [hr, hF0]
    ring
  rw [hrew, dvd_add_left (dvd_mul_right _ _), padicInt_p_pow_succ_dvd_p_pow_mul_iff,
    map_add, map_mul]

/-- **Main theorem (general `p^n → p^(n+1)` common-lift criterion):**
Let `F, G : ℤ_[p] → ℤ_[p]` vanish modulo `p^n` at `x` (`F x = p^n * cF`, `G x = p^n * cG`)
and satisfy first-order Taylor expansions modulo `p^(n+1)` with slopes `dF, dG`.
Then there exists `u : ℤ_[p]` such that `F` and `G` both vanish at `x + p^n * u` modulo
`p^(n+1)` if and only if
1. the obstruction determinant `π(cF) * π(dG) - π(cG) * π(dF)` vanishes in `ZMod p`, and
2. in the doubly singular case `π(dF) = 0 ∧ π(dG) = 0`, both normalized residues vanish
   (`π(cF) = 0 ∧ π(cG) = 0`). -/
theorem common_mod_p_pow_succ_lift_iff (p : ℕ) [Fact p.Prime] (n : ℕ)
    (F G : ℤ_[p] → ℤ_[p]) (x cF cG dF dG : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G x = (p : ℤ_[p]) ^ n * cG)
    (hF_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) ^ n * u) =
        F x + (p : ℤ_[p]) ^ n * dF * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hG_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      G (x + (p : ℤ_[p]) ^ n * u) =
        G x + (p : ℤ_[p]) ^ n * dG * u + (p : ℤ_[p]) ^ (n + 1) * r) :
    (∃ u : ℤ_[p],
        (p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u) ∧
        (p : ℤ_[p]) ^ (n + 1) ∣ G (x + (p : ℤ_[p]) ^ n * u)) ↔
      PadicInt.toZMod cF * PadicInt.toZMod dG = PadicInt.toZMod cG * PadicInt.toZMod dF ∧
      ((PadicInt.toZMod dF = 0 ∧ PadicInt.toZMod dG = 0) →
        (PadicInt.toZMod cF = 0 ∧ PadicInt.toZMod cG = 0)) := by
  rw [← field_common_linear_root_iff]
  constructor
  · rintro ⟨u, hF, hG⟩
    refine ⟨PadicInt.toZMod u, ?_, ?_⟩
    · exact (mod_p_pow_succ_lift_single_iff n F x cF dF u hF0 (hF_taylor u)).mp hF
    · exact (mod_p_pow_succ_lift_single_iff n G x cG dG u hG0 (hG_taylor u)).mp hG
  · rintro ⟨ubar, hF, hG⟩
    obtain ⟨u, hu⟩ := exists_padicInt_toZMod_eq (p := p) ubar
    refine ⟨u, ?_, ?_⟩
    · exact (mod_p_pow_succ_lift_single_iff n F x cF dF u hF0 (hF_taylor u)).mpr
        (by simpa [hu] using hF)
    · exact (mod_p_pow_succ_lift_single_iff n G x cG dG u hG0 (hG_taylor u)).mpr
        (by simpa [hu] using hG)

/-- **Obstruction-determinant exclusion corollary:**
If the obstruction determinant `π(cF) * π(dG) - π(cG) * π(dF)` is nonzero in `ZMod p`,
then no digit `u : ℤ_[p]` lifts `x` to a common root of `F` and `G` modulo `p^(n+1)`. -/
theorem no_common_lift_of_obstruction_det_ne_zero (p : ℕ) [Fact p.Prime] (n : ℕ)
    (F G : ℤ_[p] → ℤ_[p]) (x cF cG dF dG : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G x = (p : ℤ_[p]) ^ n * cG)
    (hF_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) ^ n * u) =
        F x + (p : ℤ_[p]) ^ n * dF * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hG_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      G (x + (p : ℤ_[p]) ^ n * u) =
        G x + (p : ℤ_[p]) ^ n * dG * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hdet : PadicInt.toZMod cF * PadicInt.toZMod dG -
            PadicInt.toZMod cG * PadicInt.toZMod dF ≠ 0) :
    ∀ u : ℤ_[p], ¬ ((p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u) ∧
                    (p : ℤ_[p]) ^ (n + 1) ∣ G (x + (p : ℤ_[p]) ^ n * u)) := by
  intro u hu
  have hiff := (common_mod_p_pow_succ_lift_iff p n F G x cF cG dF dG hF0 hG0 hF_taylor hG_taylor).mp
    ⟨u, hu⟩
  exact hdet (sub_eq_zero.mpr hiff.1)

/-- Uniqueness of the lifting digit `π(u)` whenever at least one reduced derivative
is nonzero. -/
theorem common_lift_digit_unique (p : ℕ) [Fact p.Prime] (n : ℕ)
    (F G : ℤ_[p] → ℤ_[p]) (x cF cG dF dG u₁ u₂ : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G x = (p : ℤ_[p]) ^ n * cG)
    (hF_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) ^ n * u) =
        F x + (p : ℤ_[p]) ^ n * dF * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hG_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      G (x + (p : ℤ_[p]) ^ n * u) =
        G x + (p : ℤ_[p]) ^ n * dG * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hnd : PadicInt.toZMod dF ≠ 0 ∨ PadicInt.toZMod dG ≠ 0)
    (h₁ : (p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u₁) ∧
          (p : ℤ_[p]) ^ (n + 1) ∣ G (x + (p : ℤ_[p]) ^ n * u₁))
    (h₂ : (p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u₂) ∧
          (p : ℤ_[p]) ^ (n + 1) ∣ G (x + (p : ℤ_[p]) ^ n * u₂)) :
    PadicInt.toZMod u₁ = PadicInt.toZMod u₂ := by
  exact field_common_linear_root_unique hnd
    ⟨(mod_p_pow_succ_lift_single_iff n F x cF dF u₁ hF0 (hF_taylor u₁)).mp h₁.1,
     (mod_p_pow_succ_lift_single_iff n G x cG dG u₁ hG0 (hG_taylor u₁)).mp h₁.2⟩
    ⟨(mod_p_pow_succ_lift_single_iff n F x cF dF u₂ hF0 (hF_taylor u₂)).mp h₂.1,
     (mod_p_pow_succ_lift_single_iff n G x cG dG u₂ hG0 (hG_taylor u₂)).mp h₂.2⟩

/-- In the doubly singular surviving case (`π(dF) = π(dG) = π(cF) = π(cG) = 0`),
every digit `u : ℤ_[p]` yields a common root modulo `p^(n+1)`. -/
theorem common_lift_all_of_doubly_singular (p : ℕ) [Fact p.Prime] (n : ℕ)
    (F G : ℤ_[p] → ℤ_[p]) (x cF cG dF dG : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G x = (p : ℤ_[p]) ^ n * cG)
    (hF_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) ^ n * u) =
        F x + (p : ℤ_[p]) ^ n * dF * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hG_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      G (x + (p : ℤ_[p]) ^ n * u) =
        G x + (p : ℤ_[p]) ^ n * dG * u + (p : ℤ_[p]) ^ (n + 1) * r)
    (hdF : PadicInt.toZMod dF = 0) (hdG : PadicInt.toZMod dG = 0)
    (hcF : PadicInt.toZMod cF = 0) (hcG : PadicInt.toZMod cG = 0)
    (u : ℤ_[p]) :
    (p : ℤ_[p]) ^ (n + 1) ∣ F (x + (p : ℤ_[p]) ^ n * u) ∧
    (p : ℤ_[p]) ^ (n + 1) ∣ G (x + (p : ℤ_[p]) ^ n * u) := by
  constructor
  · exact (mod_p_pow_succ_lift_single_iff n F x cF dF u hF0 (hF_taylor u)).mpr (by simp [hcF, hdF])
  · exact (mod_p_pow_succ_lift_single_iff n G x cG dG u hG0 (hG_taylor u)).mpr (by simp [hcG, hdG])

/-- Invariance of the criterion under shifting the mod-`p^n` representative
`x ↦ x + p^n * s`, which shifts `(cF, cG) ↦ (cF + dF * s, cG + dG * s)` modulo `p`. -/
theorem common_lift_invariant {K : Type*} [Field K] (cF dF cG dG s : K) :
    ((cF + dF * s) * dG = (cG + dG * s) * dF ∧
      ((dF = 0 ∧ dG = 0) → (cF + dF * s = 0 ∧ cG + dG * s = 0))) ↔
    (cF * dG = cG * dF ∧ ((dF = 0 ∧ dG = 0) → (cF = 0 ∧ cG = 0))) := by
  constructor <;> rintro ⟨hdet, hsing⟩ <;> refine ⟨by linear_combination hdet, ?_⟩
  · rintro ⟨hdF, hdG⟩
    simpa [hdF, hdG] using hsing ⟨hdF, hdG⟩
  · rintro ⟨hdF, hdG⟩
    simpa [hdF, hdG] using hsing ⟨hdF, hdG⟩

private theorem pow_taylor_second_order {R : Type*} [CommRing R] (k : ℕ) (a h : R) :
    ∃ r : R, (a + h) ^ k = a ^ k + (k : R) * a ^ (k - 1) * h + h ^ 2 * r := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    cases k with
    | zero => exact ⟨0, by simp⟩
    | succ m =>
      refine ⟨((m : R) + 1) * a ^ m + (a + h) * r, ?_⟩
      rw [pow_succ, hr]
      simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
      ring

/-- First-order Taylor expansion with quadratic remainder for any polynomial over a
commutative ring. -/
theorem poly_taylor_second_order {R : Type*} [CommRing R] (F : Polynomial R) (a h : R) :
    ∃ r : R, F.eval (a + h) = F.eval a + F.derivative.eval a * h + h ^ 2 * r := by
  induction F using Polynomial.induction_on' with
  | add F₁ F₂ ih₁ ih₂ =>
    obtain ⟨r₁, hr₁⟩ := ih₁
    obtain ⟨r₂, hr₂⟩ := ih₂
    refine ⟨r₁ + r₂, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add, hr₁, hr₂]
    ring
  | monomial k c =>
    obtain ⟨r, hr⟩ := pow_taylor_second_order k a h
    refine ⟨c * r, ?_⟩
    simp only [Polynomial.eval_monomial, Polynomial.derivative_monomial, hr]
    ring

private theorem poly_taylor_mod_p_pow_succ {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    (F : Polynomial ℤ_[p]) (x u : ℤ_[p]) :
    ∃ r : ℤ_[p],
      F.eval (x + (p : ℤ_[p]) ^ n * u) =
        F.eval x + (p : ℤ_[p]) ^ n * F.derivative.eval x * u + (p : ℤ_[p]) ^ (n + 1) * r := by
  obtain ⟨r, hr⟩ := poly_taylor_second_order F x ((p : ℤ_[p]) ^ n * u)
  have hexp : 2 * n = (n + 1) + (n - 1) := by omega
  refine ⟨(p : ℤ_[p]) ^ (n - 1) * u ^ 2 * r, ?_⟩
  rw [hr]
  have hp2 : ((p : ℤ_[p]) ^ n) ^ 2 = (p : ℤ_[p]) ^ (n + 1) * (p : ℤ_[p]) ^ (n - 1) := by
    rw [← pow_mul, mul_comm n 2, hexp, pow_add]
  calc
    F.eval x + F.derivative.eval x * ((p : ℤ_[p]) ^ n * u) + ((p : ℤ_[p]) ^ n * u) ^ 2 * r
      = F.eval x + (p : ℤ_[p]) ^ n * F.derivative.eval x * u +
          ((p : ℤ_[p]) ^ n) ^ 2 * u ^ 2 * r := by ring
    _ = F.eval x + (p : ℤ_[p]) ^ n * F.derivative.eval x * u +
          (p : ℤ_[p]) ^ (n + 1) * ((p : ℤ_[p]) ^ (n - 1) * u ^ 2 * r) := by
        rw [hp2]; ring

/-- Polynomial specialization of `common_mod_p_pow_succ_lift_iff` for every `n ≥ 1`. -/
theorem poly_common_mod_p_pow_succ_lift_iff (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    (F G : Polynomial ℤ_[p]) (x cF cG : ℤ_[p])
    (hF0 : F.eval x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G.eval x = (p : ℤ_[p]) ^ n * cG) :
    (∃ u : ℤ_[p],
        (p : ℤ_[p]) ^ (n + 1) ∣ F.eval (x + (p : ℤ_[p]) ^ n * u) ∧
        (p : ℤ_[p]) ^ (n + 1) ∣ G.eval (x + (p : ℤ_[p]) ^ n * u)) ↔
      PadicInt.toZMod cF * PadicInt.toZMod (G.derivative.eval x) =
        PadicInt.toZMod cG * PadicInt.toZMod (F.derivative.eval x) ∧
      ((PadicInt.toZMod (F.derivative.eval x) = 0 ∧
        PadicInt.toZMod (G.derivative.eval x) = 0) →
        (PadicInt.toZMod cF = 0 ∧ PadicInt.toZMod cG = 0)) :=
  common_mod_p_pow_succ_lift_iff p n (fun t => F.eval t) (fun t => G.eval t)
    x cF cG (F.derivative.eval x) (G.derivative.eval x) hF0 hG0
    (poly_taylor_mod_p_pow_succ hn F x) (poly_taylor_mod_p_pow_succ hn G x)

/-- Polynomial specialization of the obstruction-determinant exclusion corollary (`n ≥ 1`). -/
theorem poly_no_common_lift_of_obstruction_det_ne_zero (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n)
    (F G : Polynomial ℤ_[p]) (x cF cG : ℤ_[p])
    (hF0 : F.eval x = (p : ℤ_[p]) ^ n * cF)
    (hG0 : G.eval x = (p : ℤ_[p]) ^ n * cG)
    (hdet : PadicInt.toZMod cF * PadicInt.toZMod (G.derivative.eval x) -
            PadicInt.toZMod cG * PadicInt.toZMod (F.derivative.eval x) ≠ 0) :
    ∀ u : ℤ_[p], ¬ ((p : ℤ_[p]) ^ (n + 1) ∣ F.eval (x + (p : ℤ_[p]) ^ n * u) ∧
                    (p : ℤ_[p]) ^ (n + 1) ∣ G.eval (x + (p : ℤ_[p]) ^ n * u)) :=
  no_common_lift_of_obstruction_det_ne_zero p n (fun t => F.eval t) (fun t => G.eval t)
    x cF cG (F.derivative.eval x) (G.derivative.eval x) hF0 hG0
    (poly_taylor_mod_p_pow_succ hn F x) (poly_taylor_mod_p_pow_succ hn G x) hdet

/-- The `n = 1` (`p → p^2`) specialization of `common_mod_p_pow_succ_lift_iff`. -/
theorem common_mod_p_sq_lift_iff (p : ℕ) [Fact p.Prime]
    (F G : ℤ_[p] → ℤ_[p]) (x cF cG dF dG : ℤ_[p])
    (hF0 : F x = (p : ℤ_[p]) * cF)
    (hG0 : G x = (p : ℤ_[p]) * cG)
    (hF_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      F (x + (p : ℤ_[p]) * u) = F x + (p : ℤ_[p]) * dF * u + (p : ℤ_[p]) ^ 2 * r)
    (hG_taylor : ∀ u : ℤ_[p], ∃ r : ℤ_[p],
      G (x + (p : ℤ_[p]) * u) = G x + (p : ℤ_[p]) * dG * u + (p : ℤ_[p]) ^ 2 * r) :
    (∃ u : ℤ_[p],
        (p : ℤ_[p]) ^ 2 ∣ F (x + (p : ℤ_[p]) * u) ∧
        (p : ℤ_[p]) ^ 2 ∣ G (x + (p : ℤ_[p]) * u)) ↔
      PadicInt.toZMod cF * PadicInt.toZMod dG = PadicInt.toZMod cG * PadicInt.toZMod dF ∧
      ((PadicInt.toZMod dF = 0 ∧ PadicInt.toZMod dG = 0) →
        (PadicInt.toZMod cF = 0 ∧ PadicInt.toZMod cG = 0)) := by
  simpa only [pow_one] using
    common_mod_p_pow_succ_lift_iff p 1 F G x cF cG dF dG
      (by simpa only [pow_one] using hF0)
      (by simpa only [pow_one] using hG0)
      (by simpa only [pow_one] using hF_taylor)
      (by simpa only [pow_one] using hG_taylor)

/-- Worked example (`p = 17`, disc `a = 12` in the `(1, 0)` census):
the two linear conditions `8 + 14 * u = 0` and `15 + 16 * u = 0` in `ZMod 17`
each admit a solution (`u = 14` and `u = 15`), their obstruction determinant is
`8 * 16 - 15 * 14 = 3 ≠ 0`, and they admit no common solution in `ZMod 17`. -/
theorem witness_p17_each_solvable_no_common :
    (∃ u : ZMod 17, (8 : ZMod 17) + 14 * u = 0) ∧
    (∃ u : ZMod 17, (15 : ZMod 17) + 16 * u = 0) ∧
    ((8 : ZMod 17) * 16 - 15 * 14 = 3) ∧
    ¬ ∃ u : ZMod 17, (8 : ZMod 17) + 14 * u = 0 ∧ (15 : ZMod 17) + 16 * u = 0 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  refine ⟨⟨14, by decide⟩, ⟨15, by decide⟩, by decide, ?_⟩
  rw [field_common_linear_root_iff]
  rintro ⟨hdet, _⟩
  have hne : (8 : ZMod 17) * 16 ≠ 15 * 14 := by decide
  exact hne hdet

/-- Worked `17`-adic application (`n = 2`, lifting mod `17^2` to mod `17^3`):
any pair of integral local functions `F, G : ℤ_[17] → ℤ_[17]` vanishing mod `17^2`
at `x` with reduced residues `(8, 15)` and reduced derivatives `(14, 16)` mod `17`
has obstruction determinant `3 ≠ 0` and admits no common lift `x + 17^2 * u` mod `17^3`. -/
theorem witness_p17_no_common_mod_17_cube_lift
    [Fact (Nat.Prime 17)]
    (F G : ℤ_[17] → ℤ_[17]) (x cF cG dF dG : ℤ_[17])
    (hF0 : F x = (17 : ℤ_[17]) ^ 2 * cF)
    (hG0 : G x = (17 : ℤ_[17]) ^ 2 * cG)
    (hF_taylor : ∀ u : ℤ_[17], ∃ r : ℤ_[17],
      F (x + (17 : ℤ_[17]) ^ 2 * u) =
        F x + (17 : ℤ_[17]) ^ 2 * dF * u + (17 : ℤ_[17]) ^ 3 * r)
    (hG_taylor : ∀ u : ℤ_[17], ∃ r : ℤ_[17],
      G (x + (17 : ℤ_[17]) ^ 2 * u) =
        G x + (17 : ℤ_[17]) ^ 2 * dG * u + (17 : ℤ_[17]) ^ 3 * r)
    (hcF : PadicInt.toZMod cF = 8) (hdF : PadicInt.toZMod dF = 14)
    (hcG : PadicInt.toZMod cG = 15) (hdG : PadicInt.toZMod dG = 16) :
    ∀ u : ℤ_[17], ¬ ((17 : ℤ_[17]) ^ 3 ∣ F (x + (17 : ℤ_[17]) ^ 2 * u) ∧
                     (17 : ℤ_[17]) ^ 3 ∣ G (x + (17 : ℤ_[17]) ^ 2 * u)) := by
  apply no_common_lift_of_obstruction_det_ne_zero 17 2 F G x cF cG dF dG
    hF0 hG0 hF_taylor hG_taylor
  rw [hcF, hdF, hcG, hdG]
  decide

end BBPGrouping.CommonSecondDigit

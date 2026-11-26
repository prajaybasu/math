module

public import BBPGrouping.MirimanoffSieve
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

public section

namespace BBPGrouping.MirimanoffFamily

/-- The homogeneous cubic obtained after eliminating the local coordinate. -/
def cubic {R : Type*} [CommRing R] (k d A B C y₁ y₂ y₃ y₄ : R) : R :=
  A * d ^ 3 * y₁ ^ 2 * y₄ - B * k * d ^ 2 * y₁ * y₂ * y₃ - C * k ^ 3 * y₂ ^ 3

/-- Cancellation works even when the value of the first polylogarithm is a nonunit. -/
theorem eliminate {R : Type*} [CommRing R] [IsDomain R] (s k d A B C L y₁ y₂ y₃ y₄ : R)
    (hs : s ≠ 0) (f₂ : s * k * y₂ + d * L * y₁ = 0)
    (f₄ : s ^ 3 * A * y₄ + s ^ 2 * B * L * y₃ + C * L ^ 3 * y₁ = 0) :
    cubic k d A B C y₁ y₂ y₃ y₄ = 0 ∧
      s ^ 2 * A * d * y₄ + s * B * d * L * y₃ - C * k * L ^ 2 * y₂ = 0 := by
  have h : d * L * y₁ = -(s * k * y₂) := by linear_combination f₂
  constructor
  · suffices he : s ^ 3 * cubic k d A B C y₁ y₂ y₃ y₄ = 0 from
      (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 hs)
    calc
      _ = s ^ 3 * A * d ^ 3 * y₁ ^ 2 * y₄
          + s ^ 2 * B * d ^ 2 * y₁ * y₃ * (-(s * k * y₂)) + C * (-(s * k * y₂)) ^ 3 := by
        unfold cubic
        ring
      _ = 0 := by rw [← h]; linear_combination (d ^ 3 * y₁ ^ 2) * f₄
  · suffices he : s * (s ^ 2 * A * d * y₄ + s * B * d * L * y₃ - C * k * L ^ 2 * y₂) = 0 from
      (mul_eq_zero.mp he).resolve_left hs
    linear_combination d * f₄ - (C * L ^ 2) * f₂

/-- Convert the two local zero conditions into a quadratic test in finite polylogarithms. -/
theorem quadratic_of_local_zeros {F : Type*} [Field F] (a c₁ c₂ h L : F)
    (hd : h * (1 - a) = a) (h₁ : c₁ + h * L = 0)
    (h₂ : 2 * c₂ + 2 * c₁ * L + h * L ^ 2 = 0) :
    2 * a * ((a - 1) * c₂) + ((a - 1) * c₁) ^ 2 = 0 := by
  have e : 2 * a * c₂ - (1 - a) * c₁ ^ 2 = 0 := by
    linear_combination (1 - a) * h * h₂ - (1 - a) * (c₁ + h * L) * h₁ - 2 * c₂ * hd
  linear_combination (a - 1) * e

/-- Global disc test for any nonzero scale reducing to zero. The field values of the
unscaled finite polylogarithms are (a - 1)cᵢ. The conclusions cover singular discs too. -/
theorem disc_test (p : ℕ) [Fact p.Prime] (a c₁ c₂ c₃ c₄ : ZMod p)
    (h : ZMod p) (hh : h * (1 - a) = a)
    (s k d A B C L y₁ y₂ y₃ y₄ : ℤ_[p])
    (hs : s ≠ 0) (hs₀ : PadicInt.toZMod s = 0)
    (hk : PadicInt.toZMod k ≠ 0) (hd : PadicInt.toZMod d ≠ 0) (hC : PadicInt.toZMod C ≠ 0)
    (h₁ : PadicInt.toZMod y₁ = c₁ + h * PadicInt.toZMod L)
    (h₂ : 2 * PadicInt.toZMod y₂ =
      2 * c₂ + 2 * c₁ * PadicInt.toZMod L + h * (PadicInt.toZMod L) ^ 2)
    (hc₂ : PadicInt.toZMod L = 0 → PadicInt.toZMod y₂ = c₂)
    (hc₃ : PadicInt.toZMod L = 0 → PadicInt.toZMod y₃ = c₃)
    (hc₄ : PadicInt.toZMod L = 0 → PadicInt.toZMod y₄ = c₄)
    (f₂ : s * k * y₂ + d * L * y₁ = 0)
    (f₄ : s ^ 3 * A * y₄ + s ^ 2 * B * L * y₃ + C * L ^ 3 * y₁ = 0) :
    cubic (PadicInt.toZMod k) (PadicInt.toZMod d) (PadicInt.toZMod A)
        (PadicInt.toZMod B) (PadicInt.toZMod C) ((a - 1) * c₁) ((a - 1) * c₂)
        ((a - 1) * c₃) ((a - 1) * c₄) = 0 ∨
      2 * a * ((a - 1) * c₂) + ((a - 1) * c₁) ^ 2 = 0 := by
  obtain ⟨e₁, e₂⟩ := eliminate s k d A B C L y₁ y₂ y₃ y₄ hs f₂ f₄
  by_cases hz : PadicInt.toZMod L = 0
  · left
    have hc₁ : PadicInt.toZMod y₁ = c₁ := by simpa [hz] using h₁
    have e := congrArg PadicInt.toZMod e₁
    simp only [cubic, map_sub, map_mul, map_pow, map_zero, hc₁, hc₂ hz, hc₃ hz, hc₄ hz] at e
    unfold cubic
    linear_combination (a - 1) ^ 3 * e
  · right
    have e := congrArg PadicInt.toZMod f₂
    simp [hs₀] at e
    have t₁ : PadicInt.toZMod y₁ = 0 := by aesop
    have e' := congrArg PadicInt.toZMod e₂
    simp [hs₀] at e'
    have t₂ : PadicInt.toZMod y₂ = 0 := by aesop
    exact quadratic_of_local_zeros a c₁ c₂ h _ hh (h₁.symm.trans t₁)
      (by simpa [t₂] using h₂.symm)

/-- On a nonsingular disc the reduced depth-two polynomial has two distinct simple roots. -/
theorem simple_classes {F : Type*} [Field F] (c h d L : F)
    (hc : c ≠ 0) (hh : h ≠ 0) (hd : d ≠ 0) :
    (d * L * (c + h * L) = 0 ↔ L = 0 ∨ L = -c / h) ∧
      -c / h ≠ 0 ∧ d * (c + 2 * h * (0 : F)) ≠ 0 ∧ d * (c + 2 * h * (-c / h)) ≠ 0 := by
  have factor : c + h * L = 0 ↔ L = -c / h := by
    rw [eq_div_iff hh]
    constructor <;> intro e <;> linear_combination e
  have deriv : c + 2 * h * (-c / h) = -c := by field_simp; ring
  simp [mul_eq_zero, hd, hc, hh, factor, deriv]

/-- A short Bézout witness bounds the total number of discs before any lifting.
U times the field polynomial and V times the disc test sum to W. -/
theorem budget_of_bezout {F : Type*} [Field F] (S : Finset F)
    (D T U V W : Polynomial F) (hw : W ≠ 0) (cert : U * D + V * T = W)
    (hD : ∀ a ∈ S, D.eval a = 0) (hT : ∀ a ∈ S, T.eval a = 0) :
    S.card ≤ W.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  apply (Polynomial.mem_roots hw).mpr
  rw [Polynomial.IsRoot.def, ← cert]
  simp [hD a ha, hT a ha]

/-- The linear-algebra and root-counting step of the auxiliary-polynomial argument. -/
theorem auxiliary_count {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (J : V →ₗ[F] W) (specialize : V →ₗ[F] Polynomial F) (S : Finset F) (r n : ℕ)
    (rank : Module.finrank F W < Module.finrank F V) (faithful : Function.Injective specialize)
    (vanish : ∀ v ∈ LinearMap.ker J, ∀ a ∈ S, (Polynomial.X - Polynomial.C a) ^ r ∣ specialize v)
    (degree : ∀ v, (specialize v).natDegree ≤ n) : r * S.card ≤ n := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := J) rank)
  have hp : specialize v ≠ 0 := by simpa using faithful.ne hv0
  have hm : r • S.val ≤ (specialize v).roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, Polynomial.count_roots]
    by_cases ha : a ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup ha, mul_one]
      exact (Polynomial.le_rootMultiplicity_iff hp).2 (vanish v hv a ha)
    · simp [Multiset.count_eq_zero.mpr (show a ∉ S.val from ha)]
  have bound := (Multiset.card_le_card hm).trans ((specialize v).card_roots'.trans (degree v))
  simpa only [Multiset.card_nsmul, Finset.card_def] using bound

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Direct evaluation of the finite polylogarithm for the small exceptional prime. -/
def finiteLi11 (m : ℕ) (a : ZMod 11) : ZMod 11 :=
  ((List.range 10).map fun i => a ^ (i + 1) / ((i + 1 : ℕ) : ZMod 11) ^ m).sum

/-- The two anchor rows and the complete field test at 11, by kernel computation. -/
theorem candidates_eleven :
    (finiteLi11 4 3 / 2, finiteLi11 3 3 / 2, finiteLi11 1 3 / 2) = (7, 3, 5) ∧
    (finiteLi11 4 9 / 8, 2 * finiteLi11 3 9 / 8, 8 * finiteLi11 1 9 / 8) = (1, 1, 10) ∧
    finiteLi11 2 3 / 2 = 3 ∧
    ∀ a : ZMod 11, a ≠ 0 → a ≠ 1 →
      let y := fun m => finiteLi11 m a
      ((cubic 6 3 3 1 4 (y 1) (y 2) (y 3) (y 4) = 0 ∨ (y 1)^2 + 2*a*y 2 = 0) ↔
        a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10) ∧
      (y 1 ≠ 0 ∨ y 2 ≠ 0) ∧ ((y 2 = 0 ∧ y 4 = 0) ↔ a = 10) := by
  decide +kernel

end BBPGrouping.MirimanoffFamily

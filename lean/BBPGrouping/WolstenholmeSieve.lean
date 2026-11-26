module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

public section

namespace BBPGrouping.Wolstenholme

/-- The hypotheses are the reduced duplication formula, the trilogarithm identity at -3,
the value at -1, and the alternating cubic harmonic sum. -/
theorem cofactor {R : Type*} [CommRing R] (k u v w z c bern : R)
    (dup : w = 4 * (u + v)) (tri : 6 * (v - 2 * u) = -13 * z)
    (neg : 4 * c = -3 * z) (harm : 4 * c = bern) :
    9 * (u * (-24 * k) + 2 * k * w) = 52 * k * bern := by
  linear_combination 18 * k * dup + 12 * k * tri - 52 * k * neg + 52 * k * harm

/-- In characteristics away from the factors of 9 and 52, the two factors give an iff. -/
theorem cofactor_zero_iff {F : Type*} [Field F] (A k bern : F)
    (h9 : (9 : F) ≠ 0) (h52 : (52 : F) ≠ 0) (eqn : 9 * A = 52 * k * bern) :
    A = 0 ↔ k = 0 ∨ bern = 0 := by
  have e : 9 * A = 0 ↔ (52 : F) * k * bern = 0 := by rw [eqn]
  simpa [mul_eq_zero, h9, h52] using e

/-- Reduction of the two local equations at a prime where the first cofactor vanishes. -/
theorem screen {F : Type*} [Field F] (k s d h c₁ c₂ B C L y₁ y₂ y₃ : F)
    (first : y₁ = c₁ + h * L)
    (second : 2 * y₂ = 2 * c₂ + 2 * c₁ * L + h * L ^ 2)
    (f₂ : k * s * y₂ + d * L * y₁ = 0)
    (f₄ : s ^ 2 * B * L * y₃ + C * L ^ 3 * y₁ = 0) :
    h * (k * s + 2 * d) * L ^ 2 + 2 * c₁ * (k * s + d) * L + 2 * k * s * c₂ = 0 ∧
      (L = 0 ∨ s ^ 2 * B * y₃ + C * L ^ 2 * y₁ = 0) := by
  constructor
  · linear_combination 2 * f₂ - k * s * second - 2 * d * L * first
  · apply mul_eq_zero.mp
    linear_combination f₄

/-- Completing the square certifies that the discriminant enumerates all root classes. -/
theorem discriminant_test {F : Type*} [Field F] (u v w L : F)
    (h4 : (4 : F) ≠ 0) (hu : u ≠ 0) :
    u * L ^ 2 + v * L + w = 0 ↔ (2 * u * L + v) ^ 2 = v ^ 2 - 4 * u * w := by
  constructor
  · intro e
    linear_combination 4 * u * e
  · intro e
    have h : (4 * u) * (u * L ^ 2 + v * L + w) = 0 := by linear_combination e
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h4 hu)

end BBPGrouping.Wolstenholme

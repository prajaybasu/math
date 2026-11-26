module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

public section

namespace BBPGrouping.ProjectiveDisc

/-- Changing the centre of a residue disc shifts the two constant terms
by the same multiple of the tangent vector. -/
theorem determinant_shift {F : Type*} [CommRing F] (a b u v t : F) :
    (a + t*u)*v - (b + t*v)*u = a*v - b*u := by ring

/-- Exact compatibility of two first-order equations over the residue field,
including the zero-tangent case. -/
theorem affine_compatibility {F : Type*} [Field F] (a b u v : F) :
    (∃ t, a + u*t = 0 ∧ b + v*t = 0) ↔
    a*v = b*u ∧ (u = 0 → v = 0 → a = 0 ∧ b = 0) := by
  constructor
  · rintro ⟨t, h, k⟩
    refine ⟨by linear_combination v*h - u*k, ?_⟩
    rintro rfl rfl
    simpa using And.intro h k
  · rintro ⟨h, k⟩
    by_cases hu : u = 0
    · by_cases hv : v = 0
      · exact ⟨0, by simpa using k hu hv⟩
      · refine ⟨-b/v, ?_, ?_⟩
        · rw [hu, zero_mul, add_zero]
          exact (mul_eq_zero.mp (by simpa [hu] using h : a*v = 0)).resolve_right hv
        · field_simp
          ring
    · refine ⟨-a/u, ?_, ?_⟩
      · field_simp
        ring
      · field_simp
        linear_combination -h

/-- Norm of the function giving an order-dividing-12 witness at x=0
on the genus-three curve of Example 4.1. -/
theorem torsion_norm {R : Type*} [CommRing R] (x : R) :
    (-x^6 - 16*x^5 - 36*x^4 + 72*x^2 + 64*x + 16)^2 -
    8 * (4*x^7 + 9*x^6 - 8*x^5 - 36*x^4 - 16*x^3 + 32*x^2 + 32*x + 8) *
      (x^2 + 4*x + 2)^2 = x^12 := by ring

end BBPGrouping.ProjectiveDisc

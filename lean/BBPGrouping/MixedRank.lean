module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public section

namespace BBPGrouping.MixedRank

/-- Two square row minors certify injectivity after reduction at every prime
which does not divide their integer determinant gcd. -/
theorem injective_of_minor_gcd {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (M : Matrix κ ι ℤ) (r s : ι → κ)
    (h : ¬ (p : ℤ) ∣ GCDMonoid.gcd (M.submatrix r id).det (M.submatrix s id).det) :
    Function.Injective (M.map (Int.castRingHom (ZMod p))).mulVec := by
  let φ := Int.castRingHom (ZMod p)
  have minor (rows : ι → κ) (hn : ¬ (p : ℤ) ∣ (M.submatrix rows id).det) :
      Function.Injective (M.map φ).mulVec := by
    have nonzero : ((M.submatrix rows id).map φ).det ≠ 0 := by
      change (φ.mapMatrix (M.submatrix rows id)).det ≠ 0
      rw [← φ.map_det]
      exact fun hz => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    intro x y he
    apply Matrix.mulVec_injective_of_det_ne_zero nonzero
    exact funext fun i => congrFun he (rows i)
  by_cases hr : (p : ℤ) ∣ (M.submatrix r id).det
  · exact minor s fun hs => h (dvd_gcd hr hs)
  · exact minor r hr

end BBPGrouping.MixedRank

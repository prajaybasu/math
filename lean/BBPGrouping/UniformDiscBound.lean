module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

public section

namespace BBPGrouping.UniformDiscBound

/-- Coordinates scaled by the factorial of their index. -/
structure Jet (R : Type*) where
  y₀ : R
  y₁ : R
  y₂ : R
  y₃ : R
  y₄ : R

def Jet.shift {R : Type*} [CommRing R] (y : Jet R) (L : R) : Jet R :=
  ⟨y.y₀, y.y₁ + y.y₀ * L, y.y₂ + 2 * y.y₁ * L + y.y₀ * L ^ 2,
   y.y₃ + 3 * y.y₂ * L + 3 * y.y₁ * L ^ 2 + y.y₀ * L ^ 3,
   y.y₄ + 4 * y.y₃ * L + 6 * y.y₂ * L ^ 2 + 4 * y.y₁ * L ^ 3 + y.y₀ * L ^ 4⟩

theorem Jet.unshift {R : Type*} [CommRing R] (y : Jet R) (L : R) :
    (y.shift L).shift (-L) = y := by
  cases y
  simp only [Jet.shift, Jet.mk.injEq]
  constructor <;> (repeat' constructor) <;> ring

def Jet.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (y : Jet R) : Jet S :=
  ⟨f y.y₀, f y.y₁, f y.y₂, f y.y₃, f y.y₄⟩

/-- The inverse shift of the actual integral values reduces to the field centre jet. -/
theorem Jet.reduce_unshift {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Jet R) (y : Jet S) (L : R) (h : w.map f = y.shift (f L)) :
    (w.shift (-L)).map f = y := by
  have comm (t : R) : (w.shift t).map f = (w.map f).shift (f t) := by
    simp [Jet.map, Jet.shift, map_ofNat]
  rw [comm, h, map_neg, Jet.unshift]

/-- At X = y₁ = y₂ = 1 the depth-two equation, multiplied by two. -/
noncomputable def testQuadratic {K : Type*} [Field K] (α β : K) : Polynomial K :=
  Polynomial.C (2 * α) + Polynomial.C (2 * (α + β)) * Polynomial.X -
    Polynomial.C (α + 2 * β) * Polynomial.X ^ 2

theorem quadratic_roots {K : Type*} [Field K] [CharZero K] (α β : K) (hα : α ≠ 0)
    (r : K) (hr : (testQuadratic α β).eval r = 0) : r ≠ 0 ∧ r ≠ 1 := by
  constructor
  · rintro rfl
    simp [testQuadratic, hα] at hr
  · rintro rfl
    have e : 3 * α = 0 := by
      simp [testQuadratic] at hr
      linear_combination hr
    exact hα ((mul_eq_zero.mp e).resolve_left (by norm_num))

private theorem avoid {K : Type*} [Field K] [Infinite K] (S : Finset K) (s b : K → K)
    (hs : ∀ r ∈ S, s r ≠ 0) : ∃ u : K, ∀ r ∈ S, s r * u + b r ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset (S.image fun r => -(b r) / s r)
  refine ⟨u, fun r hr h => hu ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨r, hr, ((eq_div_iff (hs r hr)).2 (by linear_combination h)).symm⟩

/-- The quartic at X = y₁ = y₂ = 1. The last two inputs are free factorial-scaled
centre coordinates, and the three coefficients absorb the factorials of the equations. -/
def testQuartic {K : Type*} [Field K] (a b c u v t : K) : K :=
  let w := (Jet.mk (-1) 1 2 u v).shift t
  a * w.y₄ + b * t * w.y₃ + c * t ^ 3 * w.y₁

/-- Over the algebraic closure this provides a specialization with no shared finite root.
It also covers a quartic given solely by the last monomial. -/
theorem separating_specialization {K : Type*} [Field K] [CharZero K] [Infinite K] (α β a b c : K)
    (hα : α ≠ 0) (habc : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ u v : K, ∀ r : K, (testQuadratic α β).eval r = 0 → testQuartic a b c u v r ≠ 0 := by
  classical
  let S := (testQuadratic α β).roots.toFinset
  have hF : testQuadratic α β ≠ 0 := by
    intro e
    exact (quadratic_roots α β hα 0 (by simp [e])).1 rfl
  have mem (r : K) (hr : (testQuadratic α β).eval r = 0) : r ∈ S := by
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hF).mpr hr)
  let offset := testQuartic a b c 0 0
  have expand (u v r : K) : testQuartic a b c u v r =
      a * v + ((4 * a + b) * r) * u + offset r := by
    dsimp [testQuartic, Jet.shift, offset]
    ring
  by_cases ha : a ≠ 0
  · obtain ⟨v, hv⟩ := avoid S (fun _ => a) offset (fun _ _ => ha)
    exact ⟨0, v, fun r hr => by simpa [expand] using hv r (mem r hr)⟩
  by_cases hb : b ≠ 0
  · have hu : ∀ r ∈ S, b * r ≠ 0 := by
      intro r hr
      have e := (Polynomial.mem_roots hF).mp (Multiset.mem_toFinset.mp hr)
      exact mul_ne_zero hb (quadratic_roots α β hα r e).1
    obtain ⟨u, h⟩ := avoid S (fun r => b*r) offset hu
    refine ⟨u, 0, fun r hr => ?_⟩
    rw [expand]
    simpa only [not_ne_iff.mp ha, mul_zero, zero_mul, zero_add] using h r (mem r hr)
  have hc := (habc.resolve_left ha).resolve_left hb
  refine ⟨0, 0, fun r hr => ?_⟩
  obtain ⟨hr₀, hr₁⟩ := quadratic_roots α β hα r hr
  have hlin : (1 : K) + -1 * r ≠ 0 := by intro e; apply hr₁; linear_combination -e
  simpa [testQuartic, Jet.shift, not_ne_iff.mp ha, not_ne_iff.mp hb] using
    mul_ne_zero (mul_ne_zero hc (pow_ne_zero 3 hr₀)) hlin

open MvPolynomial

/-- Primitive reduction preserves every integral zero and introduces no new monomials.
Normalize the eliminated polynomial using a coefficient of maximal norm. -/
theorem primitive_reduction {σ : Type*} (p : ℕ) [Fact p.Prime]
    (P : MvPolynomial σ ℚ_[p]) (hP : P ≠ 0) :
    ∃ R : MvPolynomial σ (ZMod p), R ≠ 0 ∧ R.support ⊆ P.support ∧
      ∀ t : σ → ℤ_[p], eval (fun i => (t i : ℚ_[p])) P = 0 →
        eval (fun i => PadicInt.toZMod (t i)) R = 0 := by
  classical
  obtain ⟨j, hj, hmax⟩ := P.support.exists_max_image (fun i => ‖P.coeff i‖)
    (support_nonempty.mpr hP)
  have hc := mem_support_iff.mp hj
  let z (i : σ →₀ ℕ) : ℤ_[p] := ⟨P.coeff i / P.coeff j, by
    change ‖P.coeff i / P.coeff j‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr hc)]
    by_cases hi : i ∈ P.support
    · exact hmax i hi
    · simp [notMem_support_iff.mp hi]⟩
  let Q : MvPolynomial σ ℤ_[p] := ∑ i ∈ P.support, monomial i (z i)
  have hQ (i) : Q.coeff i = z i := by
    by_cases hi : i ∈ P.support
    · simp only [Q, coeff_sum, coeff_monomial, Finset.sum_ite_eq', ite_eq_left hi]
    · have hz : z i = 0 := Subtype.ext (by simp [z, notMem_support_iff.mp hi])
      simp only [Q, coeff_sum, coeff_monomial, Finset.sum_ite_eq', ite_eq_right hi, hz]
  let f : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have he : map f Q = C (P.coeff j)⁻¹ * P := by
    ext i
    rw [coeff_map, hQ, coeff_C_mul]
    exact div_eq_inv_mul _ _
  refine ⟨map PadicInt.toZMod Q, ?_, ?_, ?_⟩
  · have hz : z j = 1 := Subtype.ext (div_self hc)
    intro h
    have e := congrArg (fun q : MvPolynomial σ (ZMod p) => q.coeff j) h
    simp [coeff_map, hQ, hz] at e
  · intro i hi
    by_contra hn
    have hz : z i = 0 := Subtype.ext (by simp [z, notMem_support_iff.mp hn])
    exact (mem_support_iff.mp hi) (by simp [coeff_map, hQ, hz])
  · intro t ht
    have h0 : f (eval t Q) = 0 := by
      rw [map_eval, he, map_mul, eval_C]
      change (P.coeff j)⁻¹ * eval (fun i => (t i : ℚ_[p])) P = 0
      rw [ht, mul_zero]
    have h0' : eval t Q = 0 := Subtype.ext h0
    simpa only [map_eval, Function.comp_def, map_zero] using congrArg PadicInt.toZMod h0'

/-- A nonzero exact resultant supplies one field constraint for all integral common roots,
including specializations at which leading coefficients vanish. -/
theorem resultant_disc_constraint {σ : Type*} (p : ℕ) [Fact p.Prime]
    (F G : Polynomial (MvPolynomial σ ℚ_[p])) (h : F.resultant G ≠ 0)
    (hdeg : F.natDegree ≠ 0 ∨ G.natDegree ≠ 0) :
    ∃ R : MvPolynomial σ (ZMod p), R ≠ 0 ∧ R.support ⊆ (F.resultant G).support ∧
      ∀ (t : σ → ℤ_[p]) (L : ℚ_[p]),
        F.eval₂ (eval (fun i => (t i : ℚ_[p]))) L = 0 →
        G.eval₂ (eval (fun i => (t i : ℚ_[p]))) L = 0 →
        eval (fun i => PadicInt.toZMod (t i)) R = 0 := by
  obtain ⟨R, hn, hs, hz⟩ := primitive_reduction p _ h
  refine ⟨R, hn, hs, ?_⟩
  intro t L hf hg
  apply hz t
  obtain ⟨U, V, _, _, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    F G le_rfl le_rfl hdeg
  let φ := Polynomial.eval₂RingHom (eval (fun i => (t i : ℚ_[p]))) L
  have eq := congrArg φ e
  change φ F = 0 at hf
  change φ G = 0 at hg
  rw [map_add, map_mul, map_mul, hf, hg, zero_mul, zero_mul, add_zero] at eq
  simpa [φ] using eq.symm

end BBPGrouping.UniformDiscBound

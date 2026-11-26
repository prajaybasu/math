module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

public section

namespace BBPGrouping.PolylogZeroEstimate

open MvPolynomial

/-- The residue operator which lowers a polylogarithm's index. -/
noncomputable def lower {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) : MvPolynomial (Fin (n + 1)) K :=
  ∑ i : Fin n, X i.castSucc * pderiv i.succ f

theorem partial_lower {K : Type*} [CommRing K] {n : ℕ} (j : Fin n)
    (f : MvPolynomial (Fin (n + 1)) K) :
    pderiv j.castSucc (lower f) = pderiv j.succ f + lower (pderiv j.castSucc f) := by
  classical
  simp only [lower, map_sum, pderiv_mul, Finset.sum_add_distrib]
  congr 1
  · simp [pderiv_X, Pi.single_apply, Fin.castSucc_inj]
  · apply Finset.sum_congr rfl
    intro i _
    rw [pderiv_comm]

theorem horizontal_top_partials {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (h₁ : pderiv 0 f = 0) (h₀ : lower f = 0) :
    ∀ i, pderiv i f = 0 := by
  intro i
  induction i using Fin.induction with
  | zero => exact h₁
  | succ j ih =>
    have h := partial_lower j f
    rw [h₀, ih, map_zero] at h
    simpa [lower] using h.symm

/-- In the range below p, the two residue operators have only scalar joint invariants. -/
theorem horizontal_top_constant {p n : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) (ZMod p)) (ht : f.totalDegree < p)
    (h₁ : pderiv 0 f = 0) (h₀ : lower f = 0) : f = C (f.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · simp [hm]
  simp only [coeff_C, ite_eq_right (Ne.symm hm)]
  by_contra hc
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm
  have hpos : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hlt := (le_degreeOf_of_mem_support i (mem_support_iff.mpr hc)).trans_lt
    ((degreeOf_le_totalDegree f i).trans_lt ht)
  have hunit : ((m i : ℕ) : ZMod p) ≠ 0 := fun hz =>
    (Nat.not_dvd_of_pos_of_lt hpos hlt) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  let e := m - Finsupp.single i 1
  have back : e + Finsupp.single i 1 = m :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hpos)
  have ei : e i + 1 = m i := by simpa using DFunLike.congr_fun back i
  have h := coeff_pderiv (i := i) f e
  rw [horizontal_top_partials f h₁ h₀ i, back] at h
  change 0 = f.coeff m * ((e i : ZMod p) + 1) at h
  have hw : (e i : ZMod p) + 1 = (m i : ZMod p) := by
    simpa using congrArg (fun j : ℕ => (j : ZMod p)) ei
  exact (mul_ne_zero hc hunit) (by simpa only [hw] using h.symm)

open Polynomial

/-- The finite polylogarithms, including the auxiliary geometric sum at weight zero. -/
noncomputable def finiteLi (p k : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  ∑ j ∈ Finset.range (p - 1),
    Polynomial.C (((j + 1 : ℕ) : ZMod p)⁻¹ ^ k) * Polynomial.X ^ (j + 1)

theorem finiteLi_step (p k : ℕ) [Fact p.Prime] :
    Polynomial.X * (finiteLi p (k + 1)).derivative = finiteLi p k := by
  classical
  simp only [finiteLi, Polynomial.derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j + 1 < p := by have := Finset.mem_range.mp hj; omega
  have hn : ((j + 1 : ℕ) : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (Nat.succ_pos j) hjp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hcoeff : (((j + 1 : ℕ) : ZMod p)⁻¹ ^ (k + 1)) * ((j : ZMod p) + 1) =
      ((j + 1 : ℕ) : ZMod p)⁻¹ ^ k := by
    rw [← Nat.cast_add_one, pow_succ, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow_succ, Polynomial.derivative_X,
    pow_succ Polynomial.X j, ← congrArg Polynomial.C hcoeff]
  simp only [map_mul]
  ring

theorem finiteLi_first (p : ℕ) [Fact p.Prime] :
    Polynomial.X * (1 - Polynomial.X) * (finiteLi p 1).derivative =
      Polynomial.X - Polynomial.X ^ p := by
  have geom (m : ℕ) : (1 - Polynomial.X) *
      (∑ j ∈ Finset.range m, (Polynomial.X : Polynomial (ZMod p)) ^ (j + 1)) =
      Polynomial.X - Polynomial.X ^ (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ Polynomial.X (m + 1)]
      ring
  have hp := (Fact.out : p.Prime).pos
  calc
    _ = (1 - Polynomial.X) * (Polynomial.X * (finiteLi p (0 + 1)).derivative) := by ring
    _ = _ := by
      rw [finiteLi_step]
      simpa [finiteLi, Nat.sub_add_cancel hp] using geom (p - 1)

private theorem constant_of_small_derivative {p : ℕ} [Fact p.Prime] (u : Polynomial (ZMod p))
    (hu : u.natDegree < p) (h : u.derivative = 0) : u = Polynomial.C (u.coeff 0) := by
  ext i
  cases i with
  | zero => simp
  | succ i =>
    simp only [Polynomial.coeff_C, Nat.succ_ne_zero, ite_false]
    by_cases hi : u.natDegree < i + 1
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hi
    have hc := congrArg (fun f : Polynomial (ZMod p) => f.coeff i) h
    have hn : ((i + 1 : ℕ) : ZMod p) ≠ 0 := fun hz =>
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : i + 1 < p))
        ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast hn)

/-- A reduced fraction of height less than p with zero derivative is scalar.
The derivative condition is given after clearing the denominator. -/
theorem horizontal_fraction {p : ℕ} [Fact p.Prime] (u v : Polynomial (ZMod p))
    (hv : v ≠ 0) (hc : IsCoprime u v) (hu' : u.natDegree < p) (hv' : v.natDegree < p)
    (hd : u.derivative * v = u * v.derivative) :
    u = Polynomial.C (u.coeff 0) ∧ v = Polynomial.C (v.coeff 0) := by
  have dv : v ∣ v.derivative := hc.symm.dvd_of_dvd_mul_left (hd ▸ dvd_mul_left v _)
  have zeroDeriv (f : Polynomial (ZMod p)) (hf : f ∣ f.derivative) : f.derivative = 0 := by
    by_contra he
    have hdeg : f.natDegree ≠ 0 := fun e => he (Polynomial.derivative_of_natDegree_zero e)
    exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd hf he))
      (Polynomial.natDegree_derivative_lt hdeg)
  have hdv := zeroDeriv v dv
  have hdu : u.derivative = 0 := by simpa [hdv, hv] using hd
  exact ⟨constant_of_small_derivative u hu' hdu, constant_of_small_derivative v hv' hdv⟩

/-- A derivative of a reduced rational function with denominator degree below p
cannot have a simple pole. The equality is written after clearing denominators. -/
theorem no_simple_pole {p : ℕ} [Fact p.Prime] (a : ZMod p)
    (u v g b : Polynomial (ZMod p)) (hv : v ≠ 0) (hdeg : v.natDegree < p)
    (hc : IsCoprime u v) (hg : g.eval a ≠ 0)
    (he : (Polynomial.X - Polynomial.C a) * g * (u.derivative * v - u * v.derivative) =
      b * v ^ 2) : b.eval a = 0 := by
  by_cases hval : v.eval a ≠ 0
  · have e := congrArg (Polynomial.eval a) he
    simpa [Polynomial.eval_mul, hval] using e.symm
  have vz := not_ne_iff.mp hval
  obtain ⟨w, hw, hd⟩ := v.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hv a
  have wn : w.eval a ≠ 0 := fun hz => hd ((Polynomial.dvd_iff_isRoot).mpr hz)
  let T := Polynomial.X - Polynomial.C a
  have Tn : T ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have Tz : T.eval a = 0 := by simp [T]
  have Td : T.derivative = 1 := by simp [T]
  have un : u.eval a ≠ 0 := by
    obtain ⟨c, d, cd⟩ := hc
    intro uz
    have eq := congrArg (Polynomial.eval a) cd
    simp [Polynomial.eval_add, Polynomial.eval_mul, uz, vz] at eq
  generalize hn : v.rootMultiplicity a = n at hw
  cases n with
  | zero =>
    simp only [pow_zero, one_mul] at hw
    exact (wn (hw ▸ vz)).elim
  | succ n =>
    change v = T ^ (n + 1) * w at hw
    have nlt : n + 1 < p := by
      have h := Polynomial.natDegree_le_of_dvd (show T ^ (n+1) ∣ v from ⟨w, hw⟩) hv
      simpa [T, Polynomial.natDegree_pow] using h.trans_lt hdeg
    have nz : (n : ZMod p) + 1 ≠ 0 := by
      rw [← Nat.cast_add_one]
      exact fun e => Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) nlt
        ((ZMod.natCast_eq_zero_iff _ _).mp e)
    have e : T ^ (n + 1) *
        (g * (T * u.derivative * w -
          u * (Polynomial.C ((n : ZMod p) + 1) * w + T * w.derivative))) =
        T ^ (n + 1) * (b * (T ^ (n + 1) * w ^ 2)) := by
      change T * g * _ = _ at he
      rw [hw, Polynomial.derivative_mul, Polynomial.derivative_pow_succ, Td] at he
      linear_combination (norm := (simp only [pow_succ]; ring)) he
    have e' := mul_left_cancel₀ (pow_ne_zero (n + 1) Tn) e
    have z := congrArg (Polynomial.eval a) e'
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Tz, hg, un, nz, wn] at z

/-- Vanishing of both residue coefficients for a rational primitive of
a / X + b / (1 - X). -/
theorem two_residues {p : ℕ} [Fact p.Prime] (u v : Polynomial (ZMod p))
    (a b : ZMod p) (hv : v ≠ 0) (hdeg : v.natDegree < p) (hc : IsCoprime u v)
    (h : Polynomial.X * (1 - Polynomial.X) * (u.derivative * v - u * v.derivative) =
      (Polynomial.C a * (1 - Polynomial.X) + Polynomial.C b * Polynomial.X) * v ^ 2) :
    a = 0 ∧ b = 0 := by
  let R := Polynomial.C a * (1 - Polynomial.X) + Polynomial.C b * Polynomial.X
  have h₀ := no_simple_pole 0 u v (1 - Polynomial.X) R hv hdeg hc
    (by simp) (by simpa [R] using h)
  have h₁ := no_simple_pole 1 u v (-Polynomial.X) R hv hdeg hc (by simp) (by
    dsimp [R]
    rw [← h]
    simp only [map_one]
    ring)
  constructor
  · simpa [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub] using h₀
  · simpa [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub] using h₁

/-- The scaled derivative preserves the vanishing order also at order p. -/
theorem scaled_deriv_preserves {K : Type*} [Field K] (m : ℕ) (b f : Polynomial K)
    (h : Polynomial.X ^ m ∣ f) : Polynomial.X ^ m ∣ Polynomial.X * b * f.derivative := by
  obtain ⟨g, rfl⟩ := h
  cases m with
  | zero => simp
  | succ n =>
    refine ⟨b * (Polynomial.C ((n : K) + 1) * g + Polynomial.X * g.derivative), ?_⟩
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow_succ, Polynomial.derivative_X]
    simp only [pow_succ]
    ring

/-- Each determinant term takes exactly one entry from each row. -/
theorem minor_degree {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι (Polynomial K)) (d : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Units.smul_def]
  refine (Polynomial.natDegree_smul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  calc
    _ ≤ ∑ i, d (σ i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, d i := Equiv.sum_comp σ d

end BBPGrouping.PolylogZeroEstimate

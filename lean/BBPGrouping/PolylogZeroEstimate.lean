module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.RatFunc.Basic
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

open Matrix
open scoped Matrix
variable {ι κ K F : Type*} [Fintype ι] [Field K] [Field F]

/-- Independent rows admit a square nonsingular column restriction, even
when the rows span only a proper subspace of the ambient coordinate space. -/
theorem exists_pivot_minor [DecidableEq ι] [Finite κ] (M : Matrix ι κ F)
    (hi : LinearIndependent F M.row) :
    ∃ c : ι → κ, Function.Injective c ∧ (M.submatrix id c).det ≠ 0 := by
  classical
  obtain ⟨σ, f, hf, hs, hl⟩ := exists_linearIndependent' F M.col
  let : Finite σ := Finite.of_injective f hf
  let := Fintype.ofFinite σ
  have hc : Fintype.card σ = Fintype.card ι := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hl, Set.finrank, hs,
      M.finrank_span_range_col, hi.rank_matrix]
  let e := (Fintype.card_eq.mp hc).some.symm
  refine ⟨f ∘ e, hf.comp e.injective, ?_⟩
  let B := M.submatrix id (f ∘ e)
  have hb : LinearIndependent F B.col := hl.comp e e.injective
  exact (B.isUnit_iff_isUnit_det.mp (Matrix.linearIndependent_col_iff_isUnit.mp hb)).ne_zero

/-- Restrict a rational row combination to a square column minor, then
multiply by its adjugate to clear the row coefficients. -/
private theorem pivot_adjugate [DecidableEq ι] (φ : Polynomial K →+* F)
    (M : Matrix ι κ (Polynomial K))
    (c : ι → κ) (u : ι → F) (v : ι → Polynomial K)
    (hv : ∀ i, φ (v i) = (u ᵥ* M.map φ) (c i)) :
    let B := M.submatrix id c
    φ ∘ (v ᵥ* B.adjugate) = φ B.det • u := by
  intro B
  have he : φ ∘ v = u ᵥ* B.map φ := funext hv
  have hb : B.map φ * B.adjugate.map φ = φ B.det • (1 : Matrix ι ι F) := by
    ext i j
    rw [← φ.map_matrix_mul, Matrix.mul_adjugate]
    by_cases heq : i = j <;> simp [heq]
  funext j
  change φ ((v ᵥ* B.adjugate) j) = _
  rw [φ.map_vecMul, he, Matrix.vecMul_vecMul, hb, Matrix.vecMul_smul, Matrix.vecMul_one]

/-- Cramer numerators obey the same degree bound as the pivot determinant. -/
theorem pivot_row_minors [DecidableEq ι] (φ : Polynomial K →+* F) (M : Matrix ι κ (Polynomial K))
    (c : ι → κ) (i : ι) (u : ι → F) (d : ι → ℕ)
    (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (hpiv : ∀ j, (u ᵥ* M.map φ) (c j) = if i = j then 1 else 0) :
    let B := M.submatrix id c
    B.det.natDegree ≤ ∑ j, d j ∧ ∀ j,
      let n := (B.updateCol i (M.col j)).det
      n.natDegree ≤ ∑ k, d k ∧ φ n = φ B.det * (u ᵥ* M.map φ) j := by
  intro B
  refine ⟨minor_degree B d (fun k j => hd k (c j)), ?_⟩
  intro j
  constructor
  · apply minor_degree _ d
    intro k l
    by_cases h : l = i
    · subst l; simpa using hd k j
    · simpa [Matrix.updateCol_ne h, B] using hd k (c l)
  · let v : ι → Polynomial K := Pi.single i 1
    have hp : ∀ l, φ (v l) = (u ᵥ* M.map φ) (c l) := by
      intro l
      simp [v, hpiv, Pi.single_apply, eq_comm, apply_ite]
    have e := pivot_adjugate φ M c u v hp
    have eb : φ ∘ B.adjugate.row i = φ B.det • u := by simpa [v] using e
    change φ (B.cramer (M.col j) i) = _
    rw [Matrix.cramer_eq_adjugate_mulVec]
    change φ (B.adjugate.row i ⬝ᵥ M.col j) = _
    rw [φ.map_dotProduct, eb, smul_dotProduct]
    rfl

/-- A polynomial row in the rational row span has a nonzero bounded-degree
polynomial multiple in the polynomial row span. -/
theorem clear_row_span [Finite κ] (φ : Polynomial K →+* F) (hφ : Function.Injective φ)
    (M : Matrix ι κ (Polynomial K)) (v : κ → Polynomial K) (d : ι → ℕ)
    (hi : LinearIndependent F (M.map φ).row) (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (hm : φ ∘ v ∈ Submodule.span F (Set.range (M.map φ).row)) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ ∑ j, d j ∧
      ∃ b : ι → Polynomial K, b ᵥ* M = q • v := by
  classical
  obtain ⟨c, -, hc⟩ := exists_pivot_minor _ hi
  let B := M.submatrix id c
  have hq : B.det ≠ 0 := by
    intro h
    apply hc
    change (B.map φ).det = 0
    exact (φ.map_det B).symm.trans (by rw [h, map_zero])
  rw [← range_vecMulLinear] at hm
  obtain ⟨u, hu⟩ := hm
  change u ᵥ* M.map φ = φ ∘ v at hu
  let b := (v ∘ c) ᵥ* B.adjugate
  have eb : φ ∘ b = φ B.det • u :=
    pivot_adjugate φ M c u (v ∘ c) (fun i => (congrFun hu (c i)).symm)
  refine ⟨B.det, hq, minor_degree B d (fun i j => hd i (c j)), b, ?_⟩
  funext j
  apply hφ
  have h := φ.map_vecMul M b j
  simpa only [Function.comp_apply, eb, Matrix.smul_vecMul, hu, Pi.smul_apply,
    smul_eq_mul, map_mul] using h

/-- In a nonzero subspace, choose a normalized row with its first nonzero
entry as far to the right as possible. Its prefix detects zero in the subspace. -/
private theorem last_leading_row [Finite κ] [LinearOrder κ]
    (W : Submodule F (κ → F)) (hne : ∃ v ∈ W, v ≠ 0) :
    ∃ k : κ, ∃ h ∈ W, h k = 1 ∧ (∀ j < k, h j = 0) ∧
      ∀ v ∈ W, (∀ j ≤ k, v j = 0) → v = 0 := by
  classical
  let := Fintype.ofFinite κ
  let leading (j : κ) := ∃ h ∈ W, h j = 1 ∧ ∀ l < j, h l = 0
  have pick (v : κ → F) (hv : v ∈ W) (hn : v ≠ 0) :
      ∃ j, leading j ∧ v j ≠ 0 := by
    let s := Finset.univ.filter (fun j => v j ≠ 0)
    have hs : s.Nonempty := by
      by_contra he
      apply hn
      funext j
      by_contra hj
      exact he ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    let j := s.min' hs
    have hj := (Finset.mem_filter.mp (s.min'_mem hs)).2
    refine ⟨j, ⟨(v j)⁻¹ • v, W.smul_mem _ hv, inv_mul_cancel₀ hj, ?_⟩, hj⟩
    intro l hl
    have hz : v l = 0 := by
      by_contra e
      exact hl.not_ge (s.min'_le l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩))
    simp [hz]
  let s := Finset.univ.filter leading
  obtain ⟨v, hv, hn⟩ := hne
  obtain ⟨j, hj, -⟩ := pick v hv hn
  have hs : s.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let k := s.max' hs
  obtain ⟨h, hh, hk, hb⟩ := (Finset.mem_filter.mp (s.max'_mem hs)).2
  refine ⟨k, h, hh, hk, hb, ?_⟩
  intro w hw hz
  by_contra he
  obtain ⟨l, hl, hn⟩ := pick w hw he
  exact hn (hz l (s.le_max' l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)))

/-- Construct the last reduced row and its bounded polynomial representatives
directly from independent polynomial rows. The column order is the order used
for the leading monomial. A row-space element vanishing through the final
pivot is zero. -/
theorem exists_last_row_minors [Nonempty ι] [Finite κ] [LinearOrder κ]
    (φ : Polynomial K →+* F) (M : Matrix ι κ (Polynomial K)) (d : ι → ℕ)
    (hi : LinearIndependent F (M.map φ).row) (hd : ∀ i j, (M i j).natDegree ≤ d i) :
    let W := Submodule.span F (Set.range (M.map φ).row)
    ∃ k : κ, ∃ h ∈ W, h k = 1 ∧ (∀ j < k, h j = 0) ∧
      (∀ v ∈ W, (∀ j ≤ k, v j = 0) → v = 0) ∧
      ∃ q : Polynomial K, φ q ≠ 0 ∧ q.natDegree ≤ ∑ i, d i ∧
        ∀ j, ∃ n : Polynomial K, n.natDegree ≤ ∑ i, d i ∧ φ n = φ q * h j := by
  classical
  intro W
  let A := M.map φ
  let i₀ : ι := Classical.arbitrary ι
  have hrow : A.row i₀ ∈ W := Submodule.subset_span ⟨i₀, rfl⟩
  obtain ⟨k, h, hh, hk, hb, detect⟩ := last_leading_row W ⟨_, hrow, hi.ne_zero i₀⟩
  let T := {j : κ // j ≤ k}
  let A' := A.submatrix id (Subtype.val : T → κ)
  have hinj : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hi
  have hmem (u : ι → F) : u ᵥ* A ∈ W := by
    change _ ∈ Submodule.span F (Set.range A.row)
    rw [← range_vecMulLinear]
    exact ⟨u, rfl⟩
  have hprefix : LinearIndependent F A'.row := by
    apply Matrix.vecMul_injective_iff.mp
    intro u v he
    apply hinj
    apply sub_eq_zero.mp
    apply detect _ (W.sub_mem (hmem u) (hmem v))
    intro j hj
    exact sub_eq_zero.mpr (congrFun he (⟨j, hj⟩ : T))
  obtain ⟨c, hc, hdet⟩ := exists_pivot_minor A' hprefix
  let cols (i : ι) : κ := (c i).val
  let B := M.submatrix id cols
  have hdB : φ B.det ≠ 0 := by
    rw [φ.map_det]
    exact hdet
  have hm : h ∈ LinearMap.range A.vecMulLinear := by rwa [range_vecMulLinear]
  obtain ⟨u, hu⟩ := hm
  change u ᵥ* A = h at hu
  have hit : ∃ i, cols i = k := by
    by_contra! he
    have e : u ᵥ* (B.map φ) = 0 := by
      funext i
      exact (congrFun hu (cols i)).trans (hb _ (lt_of_le_of_ne (c i).property (he i)))
    have hinv := Matrix.vecMul_injective_iff.mpr
      (Matrix.linearIndependent_rows_of_det_ne_zero hdet)
    have uz : u = 0 := hinv (e.trans (Matrix.zero_vecMul _).symm)
    have hz : h = 0 := by rw [← hu, uz, Matrix.zero_vecMul]
    simp [hz] at hk
  obtain ⟨i, hi₀⟩ := hit
  have hpiv (l : ι) : (u ᵥ* M.map φ) (cols l) = if i = l then 1 else 0 := by
    change (u ᵥ* A) _ = _
    rw [hu]
    split_ifs with hil
    · simpa [← hil, hi₀] using hk
    · apply hb
      apply lt_of_le_of_ne (c l).property
      intro e
      exact hil (hc (Subtype.ext (hi₀.trans e.symm)))
  obtain ⟨hdegree, hn⟩ := pivot_row_minors φ M cols i u d hd hpiv
  refine ⟨k, h, hh, hk, hb, detect, B.det, hdB, hdegree, ?_⟩
  intro j
  obtain ⟨hle, heq⟩ := hn j
  exact ⟨_, hle, heq.trans (by rw [← hu])⟩

/-- In leading-column order the action on monomials is strictly upper
triangular. The action on coefficients is given by δ. -/
private def rowStep [Fintype κ] (δ : F → F) (T : Matrix κ κ F) (h : κ → F) (j : κ) : F :=
  δ (h j) + (h ᵥ* T) j

omit [Fintype ι] in
/-- Checking the derivative on the generators suffices for stability of their
rational span. For cyclic rows the generator checks are the shift to the next
row and the first linear dependence. -/
theorem stable_span_of_row_derivatives [Fintype κ] (A : Matrix ι κ F) (δ : F →+ F)
    (leibniz : ∀ a b, δ (a * b) = δ a * b + a * δ b) (T : Matrix κ κ F)
    (rows : ∀ i, (fun j => δ (A i j) + (A.row i ᵥ* T) j) ∈
      Submodule.span F (Set.range A.row)) :
    ∀ h ∈ Submodule.span F (Set.range A.row),
      (fun j => δ (h j) + (h ᵥ* T) j) ∈ Submodule.span F (Set.range A.row) := by
  let W := Submodule.span F (Set.range A.row)
  intro h hh
  change rowStep δ T h ∈ W
  induction hh using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact rows i
  | zero =>
    have hz : rowStep δ T 0 = 0 := by
      funext j
      simp [rowStep]
    rw [hz]
    exact W.zero_mem
  | add v w _ _ hv hw =>
    convert W.add_mem hv hw using 1
    funext j
    simp [rowStep, Matrix.add_vecMul, add_add_add_comm]
  | smul a v hv hv' =>
    convert W.add_mem (W.smul_mem (δ a) hv) (W.smul_mem a hv') using 1
    funext j
    simp [rowStep, Matrix.smul_vecMul, leibniz, mul_add, add_assoc]

/-- A stable row space contains a normalized horizontal row whose coefficients
have bounded height over the polynomial ring. -/
theorem exists_horizontal_row [Nonempty ι] [Fintype κ] [LinearOrder κ]
    (φ : Polynomial K →+* F) (M : Matrix ι κ (Polynomial K)) (d : ι → ℕ)
    (hi : LinearIndependent F (M.map φ).row) (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (δ : F → F) (hδ₀ : δ 0 = 0) (hδ₁ : δ 1 = 0)
    (T : Matrix κ κ F) (hT : ∀ i j, j ≤ i → T i j = 0)
    (stable : ∀ h ∈ Submodule.span F (Set.range (M.map φ).row),
      (fun j => δ (h j) + (h ᵥ* T) j) ∈ Submodule.span F (Set.range (M.map φ).row)) :
    ∃ k : κ, ∃ h ∈ Submodule.span F (Set.range (M.map φ).row),
      h k = 1 ∧ (∀ j, δ (h j) + (h ᵥ* T) j = 0) ∧
      ∃ q : Polynomial K, φ q ≠ 0 ∧ q.natDegree ≤ ∑ i, d i ∧
        ∀ j, ∃ n : Polynomial K, n.natDegree ≤ ∑ i, d i ∧ φ n = φ q * h j := by
  obtain ⟨k, h, hh, hk, hz, detect, height⟩ := exists_last_row_minors φ M d hi hd
  refine ⟨k, h, hh, hk, ?_, height⟩
  have zero := detect (rowStep δ T h) (stable h hh) (by
    intro j hj
    have hc : δ (h j) = 0 := by
      rcases hj.lt_or_eq with hlt | rfl
      · rw [hz j hlt, hδ₀]
      · rw [hk, hδ₁]
    change δ (h j) + ∑ i, h i * T i j = 0
    rw [hc, zero_add]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i < j
    · rw [hz i (hij.trans_le hj), zero_mul]
    · rw [hT i j (le_of_not_gt hij), mul_zero])
  exact fun j => congrFun zero j

/-- Specialize the row identity against polynomial values of the monomials.
The constant monomial evaluates to one, so the denominator survives unchanged. -/
theorem unit_row_certificate [Fintype κ] [DecidableEq κ]
    (φ : Polynomial K →+* F) (hφ : Function.Injective φ)
    (M : Matrix ι κ (Polynomial K)) (d : ι → ℕ) (oneCol : κ)
    (hi : LinearIndependent F (M.map φ).row) (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (hone : Pi.single oneCol 1 ∈ Submodule.span F (Set.range (M.map φ).row)) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ ∑ i, d i ∧ ∃ b : ι → Polynomial K,
      ∀ w : κ → Polynomial K, w oneCol = 1 → b ⬝ᵥ (M *ᵥ w) = q := by
  let v : κ → Polynomial K := Pi.single oneCol 1
  have hv : φ ∘ v = Pi.single oneCol 1 := by
    funext j
    by_cases h : j = oneCol <;> simp [v, h]
  obtain ⟨q, hq, hdeg, b, hb⟩ := clear_row_span φ hφ M v d hi hd (hv ▸ hone)
  refine ⟨q, hq, hdeg, b, ?_⟩
  intro w hw
  rw [Matrix.dotProduct_mulVec, hb, smul_dotProduct, smul_eq_mul]
  simp [v, hw]

/-- At precision one greater than the row-degree sum, the specialized rows
cannot all vanish, even when the pivot determinant has zero constant term. -/
theorem unit_row_nonvanishing [Fintype κ] [DecidableEq κ]
    (φ : Polynomial K →+* F) (hφ : Function.Injective φ)
    (M : Matrix ι κ (Polynomial K)) (d : ι → ℕ) (oneCol : κ)
    (hi : LinearIndependent F (M.map φ).row) (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (hone : Pi.single oneCol 1 ∈ Submodule.span F (Set.range (M.map φ).row))
    (w : κ → Polynomial K) (hw : w oneCol = 1) :
    ∃ i, ¬ Polynomial.X ^ ((∑ j, d j) + 1) ∣ (M *ᵥ w) i := by
  classical
  obtain ⟨q, hq, hdeg, b, hb⟩ := unit_row_certificate φ hφ M d oneCol hi hd hone
  by_contra! h
  have hdiv : Polynomial.X ^ ((∑ j, d j) + 1) ∣ q := by
    rw [← hb w hw]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (h i) _
  have hle := Polynomial.natDegree_le_of_dvd hdiv hq
  simp only [Polynomial.natDegree_X_pow] at hle
  omega

/-- Passing from a common determinant to lowest terms preserves both
degree bounds, including for zero coefficients. -/
theorem reduced_row_height (x : RatFunc K) (n q : Polynomial K)
    (hq : algebraMap (Polynomial K) (RatFunc K) q ≠ 0)
    (hn : algebraMap (Polynomial K) (RatFunc K) n =
      algebraMap (Polynomial K) (RatFunc K) q * x) :
    x.num.natDegree ≤ n.natDegree ∧ x.denom.natDegree ≤ q.natDegree := by
  have hq' : q ≠ 0 := fun e => hq (e ▸ map_zero _)
  have e : x = algebraMap _ _ n / algebraMap _ _ q := by
    apply (eq_div_iff hq).mpr
    rw [hn, mul_comm]
  refine ⟨?_, Polynomial.natDegree_le_of_dvd ((RatFunc.denom_dvd hq').mpr ⟨n, e⟩) hq'⟩
  by_cases h : n = 0
  · simp [e, h]
  · exact Polynomial.natDegree_le_of_dvd ((RatFunc.num_dvd h).mpr ⟨q, hq', e⟩) h

/-- Matrix form of the zero estimate. The differential input is stability on the generators
and the assertion that bounded horizontal rows have only a constant column.
The conclusion is already over the polynomial ring after specialization. -/
theorem nonvanishing_of_horizontal_constants [Nonempty ι] [Fintype κ] [LinearOrder κ]
    (M : Matrix ι κ (Polynomial K)) (d : ι → ℕ) (oneCol : κ)
    (hi : LinearIndependent (RatFunc K) (M.map (algebraMap _ (RatFunc K))).row)
    (hd : ∀ i j, (M i j).natDegree ≤ d i)
    (δ : RatFunc K →+ RatFunc K) (hδ₁ : δ 1 = 0)
    (leibniz : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    (T : Matrix κ κ (RatFunc K)) (hT : ∀ i j, j ≤ i → T i j = 0)
    (rows : ∀ i,
      (fun j => δ ((M.map (algebraMap _ (RatFunc K))) i j) +
        ((M.map (algebraMap _ (RatFunc K))).row i ᵥ* T) j) ∈
        Submodule.span (RatFunc K) (Set.range (M.map (algebraMap _ (RatFunc K))).row))
    (hconst : ∀ h : κ → RatFunc K, (∀ j, δ (h j) + (h ᵥ* T) j = 0) →
      (∀ j, (h j).num.natDegree ≤ ∑ i, d i) → (∀ j, (h j).denom.natDegree ≤ ∑ i, d i) →
      ∀ j ≠ oneCol, h j = 0)
    (w : κ → Polynomial K) (hw : w oneCol = 1) :
    ∃ i, ¬ Polynomial.X ^ ((∑ j, d j) + 1) ∣ (M *ᵥ w) i := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  obtain ⟨k, h, hh, hk, hδ, q, hq, hdeg, hn⟩ :=
    exists_horizontal_row φ M d hi hd δ (map_zero δ) hδ₁ T hT
      (stable_span_of_row_derivatives (M.map φ) δ leibniz T rows)
  have hheight (j : κ) : (h j).num.natDegree ≤ ∑ i, d i ∧ (h j).denom.natDegree ≤ ∑ i, d i := by
    obtain ⟨n, hd', he⟩ := hn j
    obtain ⟨hn', hq'⟩ := reduced_row_height (h j) n q hq he
    exact ⟨hn'.trans hd', hq'.trans hdeg⟩
  have hzero := hconst h hδ (fun j => (hheight j).1) (fun j => (hheight j).2)
  have he : k = oneCol := by
    by_contra he
    exact zero_ne_one ((hzero k he).symm.trans hk)
  subst k
  have heq : h = Pi.single oneCol 1 := by
    funext j
    by_cases hj : j = oneCol
    · subst j; simpa using hk
    · simpa [hj] using hzero j hj
  exact unit_row_nonvanishing φ (RatFunc.algebraMap_injective K) M d oneCol hi hd (heq ▸ hh) w hw

end BBPGrouping.PolylogZeroEstimate

module

public import BBPGrouping.PolylogZeroEstimate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

public section

namespace BBPGrouping.LogarithmicZeroEstimate

open Polynomial Matrix
open scoped Matrix
open BBPGrouping.PolylogZeroEstimate

variable {p : ℕ} [Fact p.Prime]
local notation "k" => ZMod p
local notation "K" => RatFunc (ZMod p)

noncomputable abbrev liftPoly := algebraMap (Polynomial k) K

/-- Denominator of the logarithmic connection with the specified finite poles. -/
noncomputable def poleProduct (s : Finset k) : Polynomial k :=
  ∏ a ∈ s, (X - C a)

private theorem poleProduct_ne_zero (s : Finset k) : poleProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a

private theorem eval_erased (s : Finset k) (a : k) :
    (poleProduct (s.erase a)).eval a ≠ 0 := by
  simp only [poleProduct, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_ne_zero_iff]
  exact fun b hb => sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm

/-- With all simple poles cleared, evaluate the numerator at each pole to
recover its residue. A rational derivative of bounded denominator height
cannot have any of these residues. -/
theorem finite_residues (s : Finset k) (c : k → k) (u v : Polynomial k)
    (hv : v ≠ 0) (hd : v.natDegree < p) (hc : IsCoprime u v)
    (he : poleProduct s * (u.derivative * v - u * v.derivative) =
      (∑ a ∈ s, C (c a) * poleProduct (s.erase a)) * v ^ 2) :
    ∀ a ∈ s, c a = 0 := by
  intro a ha
  have factor := Finset.mul_prod_erase s (fun b => X - C b) ha
  have e := no_simple_pole a u v (poleProduct (s.erase a)) _ hv hd hc (eval_erased s a)
    (by simpa only [poleProduct, factor] using he)
  rw [eval_finsetSum] at e
  rw [Finset.sum_eq_single a] at e
  · have e' : c a * (poleProduct (s.erase a)).eval a = 0 := by
      simpa only [poleProduct, eval_mul, eval_C] using e
    exact (mul_eq_zero.mp e').resolve_right (eval_erased s a)
  · intro b hb hba
    have hab : a ∈ s.erase b := Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    rw [Finset.prod_eq_zero hab (sub_self a), mul_zero]
  · simp [ha]

private noncomputable def crossDeriv (x : K) :=
  x.num.derivative * x.denom - x.num * x.denom.derivative

/-- The quotient-rule derivative over the rational function field. -/
noncomputable def slope (x : K) : K := liftPoly (crossDeriv x) / liftPoly (x.denom ^ 2)

private theorem scalar_of_log_derivative (s : Finset k) (c : k → k) (x : K)
    (hn : x.num.natDegree < p) (hd : x.denom.natDegree < p)
    (he : liftPoly (poleProduct s) * slope x =
      ∑ a ∈ s, RatFunc.C (c a) * liftPoly (poleProduct (s.erase a))) :
    x = RatFunc.C (x.num.coeff 0) ∧ ∀ a ∈ s, c a = 0 := by
  have hv : liftPoly (x.denom ^ 2) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ x.denom_ne_zero)
  have eq : poleProduct s * crossDeriv x =
      (∑ a ∈ s, C (c a) * poleProduct (s.erase a)) * x.denom ^ 2 := by
    apply RatFunc.algebraMap_injective k
    simp only [map_mul, map_sum, RatFunc.algebraMap_C]
    apply (div_eq_iff hv).mp
    simpa only [slope, mul_div_assoc] using he
  have residues := finite_residues s c _ _ x.denom_ne_zero hd x.isCoprime_num_denom eq
  have hz : poleProduct s * crossDeriv x = 0 := by
    rw [eq, Finset.sum_eq_zero (fun a ha => by simp [residues a ha]), zero_mul]
  have hcross := (mul_eq_zero.mp hz).resolve_left (poleProduct_ne_zero s)
  obtain ⟨hu, hv'⟩ := horizontal_fraction x.num x.denom x.denom_ne_zero
    x.isCoprime_num_denom hn hd (sub_eq_zero.mp hcross)
  have h1 : x.denom.coeff 0 = 1 := by
    have hm := x.monic_denom
    rw [hv'] at hm
    simpa [Monic] using hm
  refine ⟨?_, residues⟩
  calc
    x = liftPoly x.num / liftPoly x.denom := x.num_div_denom.symm
    _ = RatFunc.C (x.num.coeff 0) := by
      conv_lhs => rw [hu, hv', h1]
      simp [liftPoly, RatFunc.algebraMap_C]

/-- A horizontal row of height below p in a strictly triangular logarithmic
system is constant and is killed by every residue matrix. -/
theorem horizontal_row {ι : Type*} [Fintype ι] [LinearOrder ι] (s : Finset k)
    (N : k → Matrix ι ι k) (tri : ∀ a ∈ s, ∀ i j, j ≤ i → N a i j = 0)
    (h : ι → K) (hn : ∀ j, (h j).num.natDegree < p) (hd : ∀ j, (h j).denom.natDegree < p)
    (hor : ∀ j, liftPoly (poleProduct s) * slope (h j) =
      ∑ a ∈ s, (h ᵥ* (N a).map RatFunc.C) j * liftPoly (poleProduct (s.erase a))) :
    ∃ c : ι → k, h = RatFunc.C ∘ c ∧ ∀ a ∈ s, c ᵥ* N a = 0 := by
  classical
  let c (j : ι) := (h j).num.coeff 0
  have steps (j : ι) : h j = RatFunc.C (c j) ∧ ∀ a ∈ s, (c ᵥ* N a) j = 0 := by
    apply WellFounded.induction wellFounded_lt j
    intro j ih
    apply scalar_of_log_derivative s (fun a => (c ᵥ* N a) j) _ (hn j) (hd j)
    rw [hor]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    rw [RatFunc.C.map_vecMul]
    apply Finset.sum_congr rfl
    intro i _
    change h i * RatFunc.C (N a i j) = RatFunc.C (c i) * RatFunc.C (N a i j)
    by_cases hij : i < j
    · rw [(ih i hij).1]
    · rw [tri a ha i j (le_of_not_gt hij), map_zero, mul_zero, mul_zero]
  exact ⟨c, funext fun j => (steps j).1, fun a ha => funext fun j => (steps j).2 a ha⟩

/-- The cleared logarithmic coefficient matrix; the sign corresponds to the
horizontal equation Q h' = sum_a (h N_a) Q_a. -/
noncomputable def connectionMatrix {ι : Type*} (s : Finset k) (N : k → Matrix ι ι k) :
    Matrix ι ι K := Matrix.of fun i j =>
  -(∑ a ∈ s, RatFunc.C (N a i j) * liftPoly (poleProduct (s.erase a)))

private theorem connection_action {ι : Type*} [Fintype ι] (s : Finset k)
    (N : k → Matrix ι ι k) (h : ι → K) (j : ι) :
    (h ᵥ* connectionMatrix s N) j =
      -(∑ a ∈ s, (h ᵥ* (N a).map RatFunc.C) j * liftPoly (poleProduct (s.erase a))) := by
  classical
  simp only [vecMul, dotProduct, connectionMatrix, of_apply, map_apply, mul_neg,
    Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- The matrix zero estimate with the horizontal-constants hypothesis
discharged. Stability refers to the rational span of the independent input rows. -/
theorem logarithmic_nonvanishing {ι J : Type*} [Nonempty ι] [Fintype ι]
    [Fintype J] [LinearOrder J] (s : Finset k) (N : k → Matrix J J k) (unitCol : J)
    (tri : ∀ a ∈ s, ∀ i j, j ≤ i → N a i j = 0)
    (joint : ∀ c : J → k, (∀ a ∈ s, c ᵥ* N a = 0) → ∀ j ≠ unitCol, c j = 0)
    (M : Matrix ι J (Polynomial k)) (d : ι → ℕ)
    (hi : LinearIndependent K (M.map liftPoly).row)
    (hd : ∀ i j, (M i j).natDegree ≤ d i) (hp : ∑ i, d i < p)
    (stable : ∀ h ∈ Submodule.span K (Set.range (M.map liftPoly).row),
      (fun j => liftPoly (poleProduct s) * slope (h j) + (h ᵥ* connectionMatrix s N) j) ∈
        Submodule.span K (Set.range (M.map liftPoly).row))
    (w : J → Polynomial k) (hw : w unitCol = 1) :
    ∃ i, ¬ X ^ ((∑ j, d j) + 1) ∣ (M *ᵥ w) i := by
  let δ (x : K) := liftPoly (poleProduct s) * slope x
  have hδ₀ : δ 0 = 0 := by simp [δ, slope, crossDeriv]
  have hδ₁ : δ 1 = 0 := by simp [δ, slope, crossDeriv]
  have hT (i j : J) (hij : j ≤ i) : connectionMatrix s N i j = 0 := by
    simp only [connectionMatrix, of_apply, neg_eq_zero]
    exact Finset.sum_eq_zero fun a ha => by rw [tri a ha i j hij, map_zero, zero_mul]
  obtain ⟨b, h, hh, hb, hor, q, hq, hdeg, hn⟩ :=
    exists_horizontal_row liftPoly M d hi hd δ hδ₀ hδ₁ _ hT stable
  have height (j : J) : (h j).num.natDegree < p ∧ (h j).denom.natDegree < p := by
    obtain ⟨n, hd', he⟩ := hn j
    obtain ⟨h₁, h₂⟩ := reduced_row_height (h j) n q hq he
    exact ⟨(h₁.trans hd').trans_lt hp, (h₂.trans hdeg).trans_lt hp⟩
  obtain ⟨c, hc, hN⟩ := horizontal_row s N tri h (fun j => (height j).1)
    (fun j => (height j).2) (fun j => by
      have he := hor j
      rwa [connection_action, ← sub_eq_add_neg, sub_eq_zero] at he)
  have hz (j : J) (hj : j ≠ unitCol) : h j = 0 := by
    simp [hc, Function.comp_def, joint c hN j hj]
  have beq : b = unitCol := by
    by_contra ne
    exact zero_ne_one ((hz b ne).symm.trans hb)
  subst b
  have hs : h = Pi.single unitCol 1 := by
    funext j
    by_cases he : j = unitCol
    · subst j; simpa using hb
    · simpa [he] using hz j he
  exact unit_row_nonvanishing liftPoly (RatFunc.algebraMap_injective k)
    M d unitCol hi hd (hs ▸ hh) w hw

/-- In coordinates centred at the jet, evaluation intertwines the cleared
row connection with scaled differentiation to the prescribed precision. -/
theorem jet_derivative_preserves {F J : Type*} [Field F] [Fintype J]
    (m : ℕ) (b : Polynomial F) (A : Matrix J J (Polynomial F))
    (v w : J → Polynomial F)
    (jet : ∀ j, X ^ m ∣ X * b * (w j).derivative - (A *ᵥ w) j)
    (van : X ^ m ∣ v ⬝ᵥ w) :
    X ^ m ∣ (fun j => X * b * (v j).derivative + (v ᵥ* A) j) ⬝ᵥ w := by
  have scaled := scaled_deriv_preserves m b _ van
  have defect : X ^ m ∣ ∑ j, v j * (X * b * (w j).derivative - (A *ᵥ w) j) :=
    Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (jet j) _
  convert dvd_sub scaled defect using 1
  simp only [dotProduct, derivative_sum, derivative_mul, Finset.mul_sum,
    add_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have assoc := Matrix.dotProduct_mulVec v A w
  simp only [dotProduct] at assoc
  rw [assoc]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Taylor coefficient constraints on a square array admit a nonzero
solution as long as fewer than n² coefficients are prescribed to vanish. -/
theorem word_jet_kernel {F : Type*} [Field F] {n j : ℕ} (hj : j < n * n)
    (T : (Fin n × Fin n → F) →ₗ[F] (Fin j → F)) :
    ∃ b, b ≠ 0 ∧ T b = 0 := by
  by_contra! h
  have hi : Function.Injective T := by
    intro x y e
    by_contra hxy
    exact h (x - y) (sub_ne_zero.mpr hxy) (by simp [e])
  have le := LinearMap.finrank_le_finrank_of_injective hi
  exact (Nat.not_le_of_gt hj) (by simpa [Module.finrank_pi_fintype] using le)

private theorem last_supported {F : Type*} [Field F] {n : ℕ} (v : Fin (n + 1) → F)
    (hv : ∀ i : Fin n, v i.castSucc = 0) :
    v = Pi.single (Fin.last n) (v (Fin.last n)) := by
  funext j
  refine Fin.lastCases (by simp) (fun i => ?_) j
  simp [hv, Fin.castSucc_ne_last]

/-- For two shift chains the first residue leaves just their terminal rows.
A nonzero last row of the cross-block matrix removes the first terminal row
from the joint kernel. -/
theorem two_chain_kernel {F : Type*} [Field F] {r s : ℕ}
    (B : Matrix (Fin (r + 1)) (Fin (s + 1)) F) (hB : ∃ j, B (Fin.last r) j ≠ 0)
    (u : Fin (r + 1) → F) (v : Fin (s + 1) → F)
    (hu : ∀ i : Fin r, u i.castSucc = 0) (hv : ∀ i : Fin s, v i.castSucc = 0)
    (hcross : u ᵥ* B = 0) :
    u = 0 ∧ v = Pi.single (Fin.last s) (v (Fin.last s)) := by
  obtain ⟨j, hj⟩ := hB
  have he := congrFun hcross j
  rw [last_supported u hu] at he
  simp [vecMul, dotProduct, Pi.single_apply] at he
  have hz : u (Fin.last r) = 0 := he.resolve_right hj
  exact ⟨(last_supported u hu).trans (by simp [hz]), last_supported v hv⟩

end BBPGrouping.LogarithmicZeroEstimate

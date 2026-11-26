module

public import BBPGrouping.UniformDiscBound
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

public section

namespace BBPGrouping.SelmerDiscBound

open MvPolynomial
open scoped BigOperators

private noncomputable def boxEquiv (r h : ℕ) :
    { s : Fin r →₀ ℕ // ∀ i, s i ≤ h } ≃ (Fin r → Fin (h + 1)) where
  toFun s i := ⟨s.val i, Nat.lt_succ_of_le (s.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val), fun i =>
    by simpa using Nat.le_of_lt_succ (f i).isLt⟩
  left_inv s := by ext i; simp
  right_inv f := by ext i; simp

private theorem box_rank (K : Type*) [Field K] (r h : ℕ) :
    Module.finrank K (restrictDegree (Fin r) K h) = (h + 1) ^ r := by
  classical
  let e := boxEquiv r h
  let _ := Fintype.ofEquiv _ e.symm
  unfold restrictDegree
  rw [Module.finrank_eq_card_basis (basisRestrictSupport K {s : Fin r →₀ ℕ | ∀ i, s i ≤ h})]
  exact (Fintype.card_congr e).trans (by simp)

private theorem subst_box {K : Type*} [Field K] {r m D h : ℕ}
    (f : Fin r → MvPolynomial (Fin m) K) (hf : ∀ i, (f i).totalDegree ≤ D)
    (P : MvPolynomial (Fin r) K) (hp : P ∈ restrictDegree (Fin r) K h) :
    aeval f P ∈ restrictDegree (Fin m) K (r * D * h) := by
  classical
  apply restrictTotalDegree_le_restrictDegree
  rw [mem_restrictTotalDegree]
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  change (C (P.coeff e) : MvPolynomial (Fin m) K).totalDegree + _ ≤ _
  rw [totalDegree_C, zero_add]
  change (∏ i ∈ e.support, f i ^ e i).totalDegree ≤ _
  refine (totalDegree_finsetProd _ _).trans ?_
  have bound (i : Fin r) := (mem_restrictDegree _ P h).mp hp e he i
  calc
    _ ≤ ∑ _i ∈ e.support, h * D := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (by nlinarith [Nat.mul_le_mul (bound i) (hf i)])
    _ = e.support.card * (h * D) := by simp
    _ ≤ r * D * h := by
      have card := Finset.card_le_univ e.support
      simp only [Fintype.card_fin] at card
      simpa [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using Nat.mul_le_mul_right (h * D) card

/-- A relation of uniformly bounded degree in each variable for any polynomial map
from affine n-space to affine (n+1)-space over a field. -/
theorem bounded_image_relation {K : Type*} [Field K] (n D : ℕ)
    (f : Fin (n + 1) → MvPolynomial (Fin n) K) (hf : ∀ i, (f i).totalDegree ≤ D) :
    ∃ P : MvPolynomial (Fin (n + 1)) K, P ≠ 0 ∧
      P ∈ restrictDegree (Fin (n + 1)) K (((n + 1) * D + 1) ^ n) ∧ aeval f P = 0 := by
  classical
  let h := ((n + 1) * D + 1) ^ n
  let M := restrictDegree (Fin (n + 1)) K h
  let N := restrictDegree (Fin n) K ((n + 1) * D * h)
  let F : M →ₗ[K] N := ((aeval f).toLinearMap.comp M.subtype).codRestrict N
    (fun x => subst_box f hf x x.property)
  have small : Module.finrank K N < Module.finrank K M := by
    rw [show Module.finrank K N = _ from box_rank K n _,
      show Module.finrank K M = _ from box_rank K (n+1) _]
    have step : (n+1)*D*h+1 ≤ ((n+1)*D+1)*(h+1) := by nlinarith
    calc
      _ ≤ _ := Nat.pow_le_pow_left step n
      _ = h * (h+1)^n := by rw [mul_pow]
      _ < (h+1)^(n+1) := by rw [pow_succ]; nlinarith [show 0 < (h+1)^n by positivity]
  have noninj : ¬ Function.Injective F := fun inj =>
    (not_le_of_gt small) (LinearMap.finrank_le_finrank_of_injective inj)
  rw [← LinearMap.ker_eq_bot] at noninj
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot noninj
  exact ⟨x, fun e => hn (Subtype.ext e), x.property, congrArg Subtype.val (LinearMap.mem_ker.mp hx)⟩

/-- The relation survives primitive reduction and contains the reductions of all
integral image points. The source parameters may have arbitrary denominators. -/
theorem reduced_image_relation (p : ℕ) [Fact p.Prime] (n D : ℕ)
    (f : Fin (n + 1) → MvPolynomial (Fin n) ℚ_[p]) (hf : ∀ i, (f i).totalDegree ≤ D) :
    ∃ R : MvPolynomial (Fin (n + 1)) (ZMod p), R ≠ 0 ∧
      R ∈ restrictDegree (Fin (n + 1)) (ZMod p) (((n + 1) * D + 1) ^ n) ∧
      ∀ (t : Fin n → ℚ_[p]) (u : Fin (n + 1) → ℤ_[p]),
        (∀ i, eval t (f i) = (u i : ℚ_[p])) →
          eval (fun i => PadicInt.toZMod (u i)) R = 0 := by
  obtain ⟨P, hn, hb, hz⟩ := bounded_image_relation n D f hf
  obtain ⟨R, hr, hs, hroots⟩ := UniformDiscBound.primitive_reduction p P hn
  refine ⟨R, hr, (mem_restrictDegree _ _ _).mpr (fun j hj =>
    (mem_restrictDegree _ _ _).mp hb j (hs hj)), ?_⟩
  intro t u hu
  apply hroots u
  have e := MvPolynomial.comp_aeval_apply f (aeval t) P
  rw [hz, map_zero] at e
  simpa only [aeval_eq_eval, hu] using e.symm

end BBPGrouping.SelmerDiscBound

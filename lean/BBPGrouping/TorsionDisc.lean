module

public import BBPGrouping.PolylogZeroEstimate
import all BBPGrouping.PolylogZeroEstimate
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

public section

namespace BBPGrouping.TorsionDisc

open Polynomial
open PolylogZeroEstimate (finiteLi finiteLi_step finiteLi_first)

/-- Numerator of the n-th Euler derivative of 1/(1-X).
For n > 0 this is X times the ordinary Eulerian polynomial. -/
noncomputable def eulerNumerator (K : Type*) [Field K] : ℕ → Polynomial K
  | 0 => 1
  | n + 1 => X * ((1 - X) * (eulerNumerator K n).derivative +
      C ((n : K) + 1) * eulerNumerator K n)

private noncomputable def moment (p : ℕ) [Fact p.Prime] : ℕ → Polynomial (ZMod p)
  | 0 => 1 + finiteLi p 0
  | n + 1 => X * (moment p n).derivative

private theorem period (p : ℕ) [Fact p.Prime] : finiteLi p (p - 1) = finiteLi p 0 := by
  unfold finiteLi
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j + 1 < p := by have := Finset.mem_range.mp hj; omega
  have hn : ((j + 1 : ℕ) : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (Nat.succ_pos j) hjp ((ZMod.natCast_eq_zero_iff _ _).mp h)
  rw [ZMod.pow_card_sub_one_eq_one (inv_ne_zero hn), pow_zero]

private theorem moment_weight (p n m : ℕ) [Fact p.Prime] (h : n + 1 + m = p - 1) :
    moment p (n + 1) = finiteLi p m := by
  induction n generalizing m with
  | zero =>
    simp only [moment, derivative_add, derivative_one, zero_add]
    rw [← period, ← h, show 0 + 1 + m = m + 1 by omega]
    exact finiteLi_step p m
  | succ n ih =>
    change X * (moment p (n + 1)).derivative = _
    rw [ih (m + 1) (by omega), finiteLi_step]

private theorem cleared_moment (p n : ℕ) [Fact p.Prime] :
    (1 - X) ^ (n + 1) * moment p n = (1 - X ^ p) * eulerNumerator (ZMod p) n := by
  induction n with
  | zero =>
    have h := finiteLi_first p
    rw [mul_comm X (1 - X), mul_assoc, finiteLi_step p 0] at h
    simp only [moment, eulerNumerator, mul_one]
    linear_combination h
  | succ n ih =>
    have hd := congrArg derivative ih
    simp only [derivative_mul, derivative_pow_succ, derivative_sub, derivative_one,
      derivative_X, zero_sub, derivative_pow, ZMod.natCast_self, map_zero, zero_mul] at hd
    simp only [moment, eulerNumerator]
    linear_combination (norm := (simp only [pow_succ]; ring))
      X * (1 - X) * hd + X * C ((n : ZMod p) + 1) * ih

/-- The cases m = 2 and m = 4 give the two tests on the log-zero refinement. -/
theorem finiteLi_euler_numerator (p n m : ℕ) [Fact p.Prime] (hn : 0 < n)
    (h : n + m = p - 1) :
    (1 - X) ^ (n + 1) * finiteLi p m = (1 - X ^ p) * eulerNumerator (ZMod p) n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact moment_weight p j m h ▸ cleared_moment p (j + 1)

theorem finiteLi_eval_zero_iff (p n m : ℕ) [Fact p.Prime] (hn : 0 < n)
    (h : n + m = p - 1) (a : ZMod p) (ha : a ≠ 1) :
    (finiteLi p m).eval a = 0 ↔ (eulerNumerator (ZMod p) n).eval a = 0 := by
  have eq := congrArg (Polynomial.eval a) (finiteLi_euler_numerator p n m hn h)
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, ZMod.pow_card] at eq
  have h1 : 1 - a ≠ 0 := sub_ne_zero.mpr ha.symm
  simpa [h1] using Iff.of_eq (congrArg (· = 0) eq)

/-- Keep the rational roots outside 0, 1 and -1, each with multiplicity one. -/
noncomputable def admissibleFactor (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  ∏ a ∈ Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1), (X - C a)

noncomputable def extraFactor (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  GCDMonoid.gcd (admissibleFactor p)
    (GCDMonoid.gcd (eulerNumerator (ZMod p) (p - 3)) (eulerNumerator (ZMod p) (p - 5)))

/-- A linear factor of the sieve gcd corresponds exactly to a simultaneous
finite-polylogarithm zero outside the three removed residues. -/
theorem extraFactor_linear_iff (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (a : ZMod p) :
    X - C a ∣ extraFactor p ↔
      (a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1) ∧
      (finiteLi p 2).eval a = 0 ∧ (finiteLi p 4).eval a = 0 := by
  have had : X - C a ∣ admissibleFactor p ↔ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ -1 := by
    simp [admissibleFactor, dvd_iff_isRoot, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff,
      sub_eq_zero]
  rw [extraFactor, dvd_gcd_iff, dvd_gcd_iff, had, dvd_iff_isRoot, dvd_iff_isRoot]
  apply and_congr_right
  intro ha
  exact and_congr (finiteLi_eval_zero_iff p (p - 3) 2 (by omega) (by omega) a ha.2.1).symm
    (finiteLi_eval_zero_iff p (p - 5) 4 (by omega) (by omega) a ha.2.1).symm

/-- Reduction distinguishes Frobenius-fixed lifts in an integral domain. -/
theorem fixed_lift_unique {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime]
    (red : R →+* ZMod p) {z w : R} (hz : z ^ p = z) (hw : w ^ p = w)
    (hred : red z = red w) : z = w := by
  let g := ∑ i ∈ Finset.range p, z ^ i * w ^ (p - 1 - i)
  have hg : red g = 0 := by
    simp only [g, map_sum, map_mul, map_pow, hred, ← pow_add]
    calc
      _ = ∑ _i ∈ Finset.range p, (red w) ^ (p - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have := Finset.mem_range.mp hi
        congr 1
        omega
      _ = 0 := by simp
  have e : g * (z - w) = z - w := by simpa [g, hz, hw] using geom_sum₂_mul z w p
  have hunit : g - 1 ≠ 0 := by
    intro h
    have he := congrArg red (sub_eq_zero.mp h)
    simp [hg] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp (show (g - 1) * (z - w) = 0 by
    linear_combination e)).resolve_left hunit)

/-- Fixed-prime sufficiency for the (1,1) component. The hypotheses on the
two values are supplied by the Coleman reduction at a Teichmüller point. -/
theorem one_one_of_extraFactor_one {R : Type*} [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (red : R →+* ZMod p)
    (hfactor : extraFactor p = 1) (z : R) (hz : z ^ p = z)
    (h0 : red z ≠ 0) (h1 : red z ≠ 1)
    (h2 : (finiteLi p 2).eval (red z) = 0) (h4 : (finiteLi p 4).eval (red z) = 0) :
    z = -1 := by
  have ha : red z = -1 := by
    by_contra h
    have hd := (extraFactor_linear_iff p hp (red z)).mpr ⟨⟨h0, h1, h⟩, h2, h4⟩
    rw [hfactor, dvd_iff_isRoot, IsRoot.def, eval_one] at hd
    exact one_ne_zero hd
  have odd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  exact fixed_lift_unique p red hz odd.neg_one_pow (by simpa using ha)

/-- Distribution at a primitive sixth root and even-weight inversion at its
square identify the order-six value with the order-three value. The parameter
n is the weight minus one. The analytic identities are explicit hypotheses. -/
theorem sixth_root_distribution {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (f : F → F) (z : F) (hcube : z ^ 3 = -1)
    (hinv : f ((z ^ 2)⁻¹) = -f (z ^ 2))
    (hdist : (2 : F) ^ n * (f z + f (-z)) = f (z ^ 2)) :
    (2 : F) ^ n * f z = ((2 : F) ^ n + 1) * f (z ^ 2) ∧
      (f z = 0 ↔ f (z ^ 2) = 0) := by
  have hz : -z = (z ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hcube)
  rw [hz, hinv] at hdist
  have he : (2 : F) ^ n * f z = ((2 : F) ^ n + 1) * f (z ^ 2) := by
    linear_combination hdist
  have hpos : (2 : F) ^ n + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (2 ^ n))
  exact ⟨he, ⟨fun h => (mul_eq_zero.mp (he.symm.trans (by simp [h]))).resolve_left hpos,
    fun h => (mul_eq_zero.mp (he.trans (by simp [h]))).resolve_left (pow_ne_zero _ (by norm_num))⟩⟩

end BBPGrouping.TorsionDisc

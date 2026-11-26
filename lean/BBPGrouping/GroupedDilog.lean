module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Finite ring identities for evaluating the residue-class dilogarithm sums
at all powers of a unit. -/

public section

namespace BBPGrouping.GroupedDilog

open Finset

/-- When precision plus weight fits below the prime, a local Taylor
coefficient with valuation at least k - w log_p(k) is negligible at
precision N for every omitted index k ≥ N. -/
theorem local_tail_index_bound (p w N k : ℕ) (hp : 2 ≤ p)
    (hN : 0 < N) (hfit : N + w ≤ p) (hk : N ≤ k) :
    N + w * Nat.log p k ≤ k := by
  have block (e : ℕ) : N + w * (e + 1) ≤ p ^ (e + 1) := by
    induction e with
    | zero => simpa using hfit
    | succ e ih =>
      have hw : w ≤ p ^ (e + 1) := le_trans (by rw [Nat.mul_succ]; omega) ih
      calc
        N + w * (e + 2) = (N + w * (e + 1)) + w := by ring
        _ ≤ p ^ (e + 1) + p ^ (e + 1) := Nat.add_le_add ih hw
        _ = p ^ (e + 1) * 2 := by omega
        _ ≤ p ^ (e + 2) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hp
  cases h : Nat.log p k with
  | zero => simpa using hk
  | succ e =>
    have cap := Nat.pow_log_le_self p (show k ≠ 0 by omega)
    rw [h] at cap
    exact (block e).trans cap

private theorem binomial_sum_step {R : Type*} [CommRing R] (x : R) (s N : ℕ) :
    (1 - x) * (∑ j ∈ range N, ((s + 1 + j).choose (s + 1) : R) * x ^ j) =
    (∑ j ∈ range N, ((s + j).choose s : R) * x ^ j) -
      ((s + N).choose (s + 1) : R) * x ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, mul_add, ih, pow_succ]
    have h : ((s + 1 + N).choose (s + 1) : R) =
        ((s + N).choose s : R) + ((s + N).choose (s + 1) : R) := by
      rw [show s + 1 + N = (s + N) + 1 by omega, Nat.choose_succ_succ', Nat.cast_add]
    rw [show s + (N + 1) = s + 1 + N by omega, h]
    ring

/-- In a ring where x^N vanishes, the first N negative-binomial terms
invert (1-x) to any positive power, including weights three and four. -/
theorem inverse_power_of_nilpotent {R : Type*} [CommRing R] (x : R)
    (s N : ℕ) (hx : x ^ N = 0) :
    (1 - x) ^ (s + 1) * (∑ j ∈ range N, ((s + j).choose s : R) * x ^ j) = 1 := by
  induction s with
  | zero =>
    simpa [hx, mul_comm] using geom_sum_mul_neg x N
  | succ s ih =>
    have step := binomial_sum_step x s N
    rw [hx, mul_zero, sub_zero] at step
    rw [pow_succ, mul_assoc, step, ih]

/-- The weight-(s+1) inverse on the class a + p b modulo p^N. -/
theorem residue_inverse_power (p N s : ℕ) (a : (ZMod (p ^ N))ˣ) (b : ZMod (p ^ N)) :
    let x := -(p : ZMod (p ^ N)) * b * ↑(a⁻¹)
    (↑a + p * b) ^ (s + 1) * ((↑(a⁻¹) : ZMod (p ^ N)) ^ (s + 1) *
      ∑ j ∈ range N, ((s + j).choose s : ZMod (p ^ N)) * x ^ j) = 1 := by
  dsimp only
  have hp : (p : ZMod (p ^ N)) ^ N = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hn : (-(p : ZMod (p ^ N)) * b * ↑(a⁻¹)) ^ N = 0 := by
    rw [mul_pow, mul_pow, neg_pow, hp]
    ring
  have eq : (↑a + (p : ZMod (p ^ N)) * b) * ↑(a⁻¹) = 1 - (-↑p * b * ↑(a⁻¹)) := by
    rw [add_mul, Units.mul_inv]
    ring
  rw [← mul_assoc, ← mul_pow, eq]
  exact inverse_power_of_nilpotent _ s N hn

/-- Exact remainder for the negative-binomial expansion at weight two. -/
theorem reciprocal_square_remainder {R : Type*} [CommRing R] (u : R) (N : ℕ) :
    (1 + u) ^ 2 * (∑ j ∈ range N, (j + 1 : R) * (-u) ^ j) =
    1 - (-u) ^ N * (1 + (N : R) * (1 + u)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    push_cast
    ring

/-- A unit times 1+u has an explicit inverse square when u^N vanishes.
For the computation, u is pb/a in Z/(p^N) and a is prime to p. -/
theorem grouped_inverse_square {R : Type*} [CommRing R] (a : Rˣ) (u : R)
    (N : ℕ) (hu : u ^ N = 0) :
    ((a : R) * (1 + u)) ^ 2 *
      ((↑(a⁻¹) : R) ^ 2 * ∑ j ∈ range N, (j + 1 : R) * (-u) ^ j) = 1 := by
  have hz : (-u) ^ N = 0 := by rw [neg_pow, hu, mul_zero]
  have hs := reciprocal_square_remainder u N
  rw [hz, zero_mul, sub_zero] at hs
  calc
    _ = ((↑a : R) * ↑(a⁻¹)) ^ 2 * ((1 + u) ^ 2 *
        ∑ j ∈ range N, (j + 1 : R) * (-u) ^ j) := by ring
    _ = 1 := by simp [hs]

/-- The denominator factor in a+p b is a unit at every precision p^N
whenever a is a unit. The polynomial is its inverse square. -/
theorem residue_inverse_square (p N : ℕ) (a : (ZMod (p ^ N))ˣ) (b : ZMod (p ^ N)) :
    let u := (p : ZMod (p ^ N)) * (b * ↑(a⁻¹))
    (↑a + p * b) ^ 2 * ((↑(a⁻¹) : ZMod (p ^ N)) ^ 2 *
      ∑ j ∈ range N, (j + 1 : ZMod (p ^ N)) * (-u) ^ j) = 1 := by
  dsimp only
  have hp : (p : ZMod (p ^ N)) ^ N = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hz : ((p : ZMod (p ^ N)) * (b * ↑(a⁻¹))) ^ N = 0 := by rw [mul_pow, hp, zero_mul]
  have ha : (↑a : ZMod (p ^ N)) * (1 + p * (b * ↑(a⁻¹))) = ↑a + p * b := by
    rw [mul_add, mul_one]
    congr 1
    calc
      _ = ((↑a : ZMod (p ^ N)) * ↑(a⁻¹)) * (p * b) := by ring
      _ = _ := by simp
  simpa only [ha] using grouped_inverse_square a _ N hz

/-- Finite geometric sums telescope against translation by one. -/
private theorem moment_shift {R : Type*} [CommRing R] (z : R) (f : R → R)
    (length : ℕ) :
    (∑ k ∈ range length, z ^ k * f k) -
      z * (∑ k ∈ range length, z ^ k * f (k + 1)) =
      f 0 - z ^ length * f length := by
  induction length with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, Nat.cast_succ, pow_succ]
    linear_combination ih

/-- The normalized finite moments have the same shift law as the geometric
measure when the block length vanishes in the coefficient ring. -/
theorem normalized_moment_shift {R : Type*} [CommRing R] (z : R) (f : R → R)
    (length : ℕ) (hl : (length : R) = 0) (scale : R)
    (hs : scale * (1 - z ^ length) = 1) :
    scale * (∑ k ∈ range length, z ^ k * f k) -
      z * (scale * ∑ k ∈ range length, z ^ k * f (k + 1)) = f 0 := by
  have shift := moment_shift z f length
  rw [hl] at shift
  linear_combination scale * shift + f 0 * hs

/-- The recurrence used to compute the normalized geometric moments. The
constant term on the right gives 1 in degree zero and 0 in positive degree. -/
theorem geometric_moment_recurrence {R : Type*} [CommRing R] (z scale : R)
    (length : ℕ) (hl : (length : R) = 0) (hs : scale * (1 - z ^ length) = 1)
    (j : ℕ) :
    let moment := fun i : ℕ => scale * ∑ b ∈ range length, z ^ b * (b : R) ^ i
    (1 - z) * moment j = (0 : R) ^ j +
      z * ∑ i ∈ range j, (j.choose i : R) * moment i := by
  dsimp only
  have translated :
      scale * (∑ b ∈ range length, z ^ b * ((b : R) + 1) ^ j) =
      ∑ i ∈ range (j + 1), (j.choose i : R) *
        (scale * ∑ b ∈ range length, z ^ b * (b : R) ^ i) := by
    simp_rw [add_pow, one_pow, mul_one, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro b _
    ring
  rw [sum_range_succ] at translated
  simp only [Nat.choose_self, Nat.cast_one, one_mul] at translated
  have shift := normalized_moment_shift z (fun x : R => x ^ j) length hl scale hs
  rw [translated] at shift
  linear_combination shift

/-- The finite positive-weight sum on one residue class factors through its first
N geometric moments. The normalization and the block length are arbitrary.
Each d b represents the unit a + p b in the coefficient ring. -/
theorem residue_power_moments (p N length s : ℕ) (a : (ZMod (p ^ N))ˣ)
    (d : ℕ → (ZMod (p ^ N))ˣ) (hd : ∀ b, (d b : ZMod (p ^ N)) = ↑a + p * b)
    (z scale : ZMod (p ^ N)) :
    scale * (∑ b ∈ range length, z ^ b * (↑((d b)⁻¹) : ZMod (p ^ N)) ^ (s + 1)) =
    ∑ j ∈ range N, (((s + j).choose s : ZMod (p ^ N)) * (↑(a⁻¹) : ZMod (p ^ N)) ^ (s + 1) *
      (-(p : ZMod (p ^ N)) * ↑(a⁻¹)) ^ j) *
      (scale * ∑ b ∈ range length, z ^ b * (b : ZMod (p ^ N)) ^ j) := by
  have term (b : ℕ) := residue_inverse_power p N s a (b : ZMod (p ^ N))
  simp only [← hd] at term
  have unit_pow (v : (ZMod (p ^ N))ˣ) :
      (↑(v⁻¹) : ZMod (p ^ N)) ^ (s + 1) * (v : ZMod (p ^ N)) ^ (s + 1) = 1 := by
    rw [← mul_pow]; simp
  have expand (b : ℕ) := congrArg
    (fun x : ZMod (p ^ N) => (↑((d b)⁻¹) : ZMod (p ^ N)) ^ (s + 1) * x) (term b)
  simp only [← mul_assoc, unit_pow, one_mul, mul_one] at expand
  simp_rw [← expand, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro b _
  have fac : -(p : ZMod (p ^ N)) * b * ↑(a⁻¹) =
      (-(p : ZMod (p ^ N)) * ↑(a⁻¹)) * b := by ring
  rw [fac, mul_pow]
  ring

/-- The finite weight-two sum on one residue class factors through its first
N geometric moments. The normalization and the block length are arbitrary.
Each d b represents the unit a + p b in the coefficient ring. -/
theorem residue_square_moments (p N length : ℕ) (a : (ZMod (p ^ N))ˣ)
    (d : ℕ → (ZMod (p ^ N))ˣ) (hd : ∀ b, (d b : ZMod (p ^ N)) = ↑a + p * b)
    (z scale : ZMod (p ^ N)) :
    scale * (∑ b ∈ range length, z ^ b * (↑((d b)⁻¹) : ZMod (p ^ N)) ^ 2) =
    ∑ j ∈ range N, ((j + 1 : ZMod (p ^ N)) * (↑(a⁻¹) : ZMod (p ^ N)) ^ 2 *
      (-(p : ZMod (p ^ N)) * ↑(a⁻¹)) ^ j) *
      (scale * ∑ b ∈ range length, z ^ b * (b : ZMod (p ^ N)) ^ j) := by
  simpa [Nat.add_comm] using residue_power_moments p N length 1 a d hd z scale

/-- Triangular number used in the convolution indices. -/
def triangle (n : ℕ) : ℕ := n.choose 2

private theorem triangle_add (i j : ℕ) :
    triangle (i + j) = triangle i + triangle j + i * j := by
  induction j with
  | zero => simp [triangle]
  | succ j ih =>
    have step (k : ℕ) : triangle (k + 1) = triangle k + k := by
      simp [triangle, Nat.choose_succ_succ, add_comm]
    rw [← Nat.add_assoc, step, ih, step, Nat.mul_succ]
    omega

/-- Values at powers of w use one cross-correlation of the scaled coefficient
vector with the triangular powers. This holds even for composite moduli and
even transform lengths. -/
theorem batch_evaluation {R : Type*} [CommRing R] (w : Rˣ)
    (c : ℕ → R) (length index : ℕ) :
    (∑ i ∈ range length, c i * (((w : R) ^ index) ^ i)) =
    (↑(w ^ (-(triangle index : ℤ))) : R) *
      ∑ i ∈ range length, (c i * (↑(w ^ (-(triangle i : ℤ))) : R)) *
        (↑(w ^ (triangle (i + index) : ℤ)) : R) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have h : w ^ ((index * i : ℕ) : ℤ) =
      w ^ (-(triangle index : ℤ)) * w ^ (-(triangle i : ℤ)) *
      w ^ (triangle (i + index) : ℤ) := by
    rw [← zpow_add, ← zpow_add, triangle_add]
    push_cast
    congr 1
    ring
  have he := congrArg (fun v : Rˣ => (v : R)) h
  simp only [zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val] at he
  rw [← pow_mul, he]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val]
  ring

end BBPGrouping.GroupedDilog

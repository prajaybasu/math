module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Soundness of the exceptional-prime (Mirimanoff) depth-4 Chabauty–Kim sieve

We formalize the soundness theorem for the finite-field sieve used at the base-3
Wieferich ("Mirimanoff") prime `p = 1,006,003` for `S = {2, 3}` in depth 4
(`mirimanoff_pilot.py`, lines 48–76):

Every common `p`-adic root `(L, Y1, Y2, Y3, Y4)` in `ℤ_[p]` of the two depth-4
Chabauty–Kim functions
  `f₂(L) = p^5 · l2 · l3 · Y2 + p^4 · c23 · L · Y1 = 0`
  `f₄(L) = p^16 · A · Y4 + p^15 · B · L · Y3 + p^13 · C · L^3 · Y1 = 0`
on residue disc `a ∈ (ZMod p) \ {0, 1}` must satisfy one of the three finite-field
survivor conditions checked by the sieve:
1. Unresolved singular disc: `c1 = 0 ∧ c2 = 0`,
2. Log-zero branch: `c1 ≠ 0` and `π(A)·c4 + π(B)·u·c3 + π(C)·u^3·c1 = 0`
   with `u = -π(l2)·π(l3)·π(c23)⁻¹·c2·c1⁻¹`,
3. `Li₁`-zero branch: `c1 ≠ 0` and `2·c2·a - c1^2·(1 - a) = 0`.

We also prove `one_one_sieve_sound` for the `(1, 1)` component.
-/

public section

namespace BBPGrouping

private theorem padicInt_p_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℤ_[p]) ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  exact_mod_cast hp

private theorem padicInt_dvd_of_toZMod_eq_zero {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (hx : PadicInt.toZMod x = 0) : ∃ y : ℤ_[p], x = (p : ℤ_[p]) * y := by
  have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hx
  have hnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hmem
  have hnorm : ‖x‖ < 1 :=
    lt_of_le_of_ne (PadicInt.norm_le_one x) (fun h1 => hnu (PadicInt.isUnit_iff.mpr h1))
  exact (PadicInt.norm_lt_one_iff_dvd x).mp hnorm

private theorem padicInt_toZMod_eq_zero_of_mul_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) :
    PadicInt.toZMod ((p : ℤ_[p]) * y) = 0 := by
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- **Soundness of the Mirimanoff depth-4 Chabauty–Kim sieve:**
Any common `p`-adic root in `ℤ_[p]` on residue disc `a ∈ (ZMod p) \ {0, 1}`
survives at least one of the three finite-field sieve tests (unresolved singular,
log-zero branch, or `Li₁`-zero branch). -/
theorem mirimanoff_sieve_sound (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a c1 c2 c3 c4 : ZMod p) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (l2 l3 c23 A B C L Y1 Y2 Y3 Y4 : ℤ_[p])
    (hl2 : PadicInt.toZMod l2 ≠ 0) (hl3 : PadicInt.toZMod l3 ≠ 0)
    (hc23 : PadicInt.toZMod c23 ≠ 0) (hC : PadicInt.toZMod C ≠ 0)
    (hY1 : PadicInt.toZMod Y1 = c1 + (a * (1 - a)⁻¹) * PadicInt.toZMod L)
    (hY2 : PadicInt.toZMod Y2 =
      c2 + c1 * PadicInt.toZMod L + (a * (1 - a)⁻¹) * (2 : ZMod p)⁻¹ * (PadicInt.toZMod L) ^ 2)
    (hY3 : PadicInt.toZMod L = 0 → PadicInt.toZMod Y3 = c3)
    (hY4 : PadicInt.toZMod L = 0 → PadicInt.toZMod Y4 = c4)
    (hf2 : (p : ℤ_[p]) ^ 5 * l2 * l3 * Y2 + (p : ℤ_[p]) ^ 4 * c23 * L * Y1 = 0)
    (hf4 : (p : ℤ_[p]) ^ 16 * A * Y4 + (p : ℤ_[p]) ^ 15 * B * L * Y3 +
      (p : ℤ_[p]) ^ 13 * C * L ^ 3 * Y1 = 0) :
    (c1 = 0 ∧ c2 = 0) ∨
    (c1 ≠ 0 ∧
      let u := -(PadicInt.toZMod l2 * PadicInt.toZMod l3 * (PadicInt.toZMod c23)⁻¹) * c2 * c1⁻¹
      PadicInt.toZMod A * c4 + PadicInt.toZMod B * u * c3 +
        PadicInt.toZMod C * u ^ 3 * c1 = 0) ∨
    (c1 ≠ 0 ∧ 2 * c2 * a - c1 ^ 2 * (1 - a) = 0) := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := padicInt_p_ne_zero p
  have h1a : (1 : ZMod p) - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have hh : a * (1 - a)⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero h1a)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    have hprime : p.Prime := Fact.out
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hge := hprime.two_le
    omega
  -- Divide f2 by p^4 to obtain p * l2 * l3 * Y2 + c23 * L * Y1 = 0.
  have hf2_4 : (p : ℤ_[p]) * l2 * l3 * Y2 + c23 * L * Y1 = 0 := by
    have h : (p : ℤ_[p]) ^ 4 * ((p : ℤ_[p]) * l2 * l3 * Y2 + c23 * L * Y1) = 0 := by
      linear_combination hf2
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 4 hp0)
  -- Reduce mod p: c23 * L * Y1 ≡ 0 (mod p), hence L ≡ 0 or Y1 ≡ 0 (mod p).
  have hLY1 : PadicInt.toZMod L = 0 ∨ PadicInt.toZMod Y1 = 0 := by
    have hmod := congrArg PadicInt.toZMod hf2_4
    rw [map_add, map_zero] at hmod
    have hterm1 : PadicInt.toZMod ((p : ℤ_[p]) * l2 * l3 * Y2) = 0 := by
      have : (p : ℤ_[p]) * l2 * l3 * Y2 = (p : ℤ_[p]) * (l2 * l3 * Y2) := by ring
      rw [this]
      exact padicInt_toZMod_eq_zero_of_mul_p _
    rw [hterm1, zero_add, map_mul, map_mul] at hmod
    have h1 := (mul_eq_zero.mp hmod)
    rcases h1 with hL | hY
    · left; exact (mul_eq_zero.mp hL).resolve_left hc23
    · right; exact hY
  -- Case split on whether c1 = 0 (singular disc) or c1 ≠ 0.
  by_cases hc1 : c1 = 0
  · -- Case 0: Singular disc (c1 = 0). Both L and Y1 vanish mod p, so p^5 | f2 gives c2 = 0.
    left
    refine ⟨hc1, ?_⟩
    have hL0 : PadicInt.toZMod L = 0 := by
      rcases hLY1 with hL | hY
      · exact hL
      · rw [hc1, zero_add] at hY1
        rw [hY] at hY1
        exact (mul_eq_zero.mp hY1.symm).resolve_left hh
    have hY1_0 : PadicInt.toZMod Y1 = 0 := by rw [hY1, hc1, hL0, mul_zero, add_zero]
    obtain ⟨u, hu⟩ := padicInt_dvd_of_toZMod_eq_zero hL0
    obtain ⟨v, hv⟩ := padicInt_dvd_of_toZMod_eq_zero hY1_0
    have hf2_5 : l2 * l3 * Y2 + (p : ℤ_[p]) * c23 * u * v = 0 := by
      have h : (p : ℤ_[p]) * (l2 * l3 * Y2 + (p : ℤ_[p]) * c23 * u * v) = 0 := by
        linear_combination hf2_4 - c23 * Y1 * hu - c23 * ((p : ℤ_[p]) * u) * hv
      exact (mul_eq_zero.mp h).resolve_left hp0
    have hmod := congrArg PadicInt.toZMod hf2_5
    rw [map_add, map_zero] at hmod
    have hterm2 : PadicInt.toZMod ((p : ℤ_[p]) * c23 * u * v) = 0 := by
      have : (p : ℤ_[p]) * c23 * u * v = (p : ℤ_[p]) * (c23 * u * v) := by ring
      rw [this]
      exact padicInt_toZMod_eq_zero_of_mul_p _
    rw [hterm2, add_zero, map_mul, map_mul] at hmod
    have hY2_0 : PadicInt.toZMod Y2 = 0 :=
      (mul_eq_zero.mp hmod).resolve_left (mul_ne_zero hl2 hl3)
    rw [hY2, hL0] at hY2_0
    simpa using hY2_0
  · -- Non-singular disc (c1 ≠ 0).
    rcases hLY1 with hL0 | hY1_0
    · -- Case 1: Log-zero branch (L = p * u).
      right; left
      refine ⟨hc1, ?_⟩
      obtain ⟨u, hu⟩ := padicInt_dvd_of_toZMod_eq_zero hL0
      have hf2_5 : l2 * l3 * Y2 + c23 * u * Y1 = 0 := by
        have h : (p : ℤ_[p]) * (l2 * l3 * Y2 + c23 * u * Y1) = 0 := by
          linear_combination hf2_4 - c23 * Y1 * hu
        exact (mul_eq_zero.mp h).resolve_left hp0
      have hY1_c1 : PadicInt.toZMod Y1 = c1 := by rw [hY1, hL0, mul_zero, add_zero]
      have hY2_c2 : PadicInt.toZMod Y2 = c2 := by rw [hY2, hL0]; simp
      have hu_eq : PadicInt.toZMod u =
          -(PadicInt.toZMod l2 * PadicInt.toZMod l3 * (PadicInt.toZMod c23)⁻¹) * c2 * c1⁻¹ := by
        have hmod := congrArg PadicInt.toZMod hf2_5
        simp only [map_add, map_mul, map_zero, hY1_c1, hY2_c2] at hmod
        have hprod : PadicInt.toZMod c23 * c1 * PadicInt.toZMod u =
            -(PadicInt.toZMod l2 * PadicInt.toZMod l3 * c2) := by
          linear_combination hmod
        have hne : PadicInt.toZMod c23 * c1 ≠ 0 := mul_ne_zero hc23 hc1
        field_simp [hc23, hc1]
        linear_combination hprod
      -- All three terms of f4 align at p^16.
      have hf4_16 : A * Y4 + B * u * Y3 + C * u ^ 3 * Y1 = 0 := by
        have h : (p : ℤ_[p]) ^ 16 * (A * Y4 + B * u * Y3 + C * u ^ 3 * Y1) = 0 := by
          rw [hu] at hf4
          linear_combination hf4
        exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 16 hp0)
      have hmod := congrArg PadicInt.toZMod hf4_16
      simp only [map_add, map_mul, map_pow, map_zero, hY1_c1, hY3 hL0, hY4 hL0, hu_eq] at hmod
      exact hmod
    · -- Case 2: Li₁-zero branch (Y1 = p * v).
      -- Note: since c1 ≠ 0 and Y1 ≡ 0 (mod p), L cannot vanish mod p.
      have hLne : PadicInt.toZMod L ≠ 0 := by
        intro hL0
        rw [hL0, mul_zero, add_zero] at hY1
        exact hc1 (hY1.symm.trans hY1_0)
      right; right
      refine ⟨hc1, ?_⟩
      obtain ⟨v, hv⟩ := padicInt_dvd_of_toZMod_eq_zero hY1_0
      -- Divide f4 by p^14: p^2 * A * Y4 + p * B * L * Y3 + C * L^3 * v = 0.
      have hf4_14 : (p : ℤ_[p]) ^ 2 * A * Y4 + (p : ℤ_[p]) * B * L * Y3 + C * L ^ 3 * v = 0 := by
        have h : (p : ℤ_[p]) ^ 14 *
            ((p : ℤ_[p]) ^ 2 * A * Y4 + (p : ℤ_[p]) * B * L * Y3 + C * L ^ 3 * v) = 0 := by
          rw [hv] at hf4
          linear_combination hf4
        exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 14 hp0)
      -- Reduce mod p: C * L^3 * v ≡ 0, forcing v ≡ 0 (mod p).
      have hv0 : PadicInt.toZMod v = 0 := by
        have hmod := congrArg PadicInt.toZMod hf4_14
        rw [map_add, map_add, map_zero] at hmod
        have ht1 : PadicInt.toZMod ((p : ℤ_[p]) ^ 2 * A * Y4) = 0 := by
          have : (p : ℤ_[p]) ^ 2 * A * Y4 = (p : ℤ_[p]) * ((p : ℤ_[p]) * A * Y4) := by ring
          rw [this]; exact padicInt_toZMod_eq_zero_of_mul_p _
        have ht2 : PadicInt.toZMod ((p : ℤ_[p]) * B * L * Y3) = 0 := by
          have : (p : ℤ_[p]) * B * L * Y3 = (p : ℤ_[p]) * (B * L * Y3) := by ring
          rw [this]; exact padicInt_toZMod_eq_zero_of_mul_p _
        rw [ht1, ht2, zero_add, zero_add, map_mul, map_mul, map_pow] at hmod
        exact (mul_eq_zero.mp hmod).resolve_left (mul_ne_zero hC (pow_ne_zero 3 hLne))
      obtain ⟨w, hw⟩ := padicInt_dvd_of_toZMod_eq_zero hv0
      -- Plug Y1 = p^2 * w into f2/p^5: l2 * l3 * Y2 + p * c23 * L * w = 0 => Y2 ≡ 0 (mod p).
      have hf2_5 : l2 * l3 * Y2 + (p : ℤ_[p]) * c23 * L * w = 0 := by
        have h : (p : ℤ_[p]) * (l2 * l3 * Y2 + (p : ℤ_[p]) * c23 * L * w) = 0 := by
          rw [hv, hw] at hf2_4
          linear_combination hf2_4
        exact (mul_eq_zero.mp h).resolve_left hp0
      have hY2_0 : PadicInt.toZMod Y2 = 0 := by
        have hmod := congrArg PadicInt.toZMod hf2_5
        rw [map_add, map_zero] at hmod
        have ht2 : PadicInt.toZMod ((p : ℤ_[p]) * c23 * L * w) = 0 := by
          have : (p : ℤ_[p]) * c23 * L * w = (p : ℤ_[p]) * (c23 * L * w) := by ring
          rw [this]; exact padicInt_toZMod_eq_zero_of_mul_p _
        rw [ht2, add_zero, map_mul, map_mul] at hmod
        exact (mul_eq_zero.mp hmod).resolve_left (mul_ne_zero hl2 hl3)
      -- Eliminate L from c1 + h*L = 0 and c2 + c1*L + (h/2)*L^2 = 0.
      have h1 : c1 + (a * (1 - a)⁻¹) * PadicInt.toZMod L = 0 := hY1.symm.trans hY1_0
      have h2 : c2 + c1 * PadicInt.toZMod L +
          (a * (1 - a)⁻¹) * (2 : ZMod p)⁻¹ * (PadicInt.toZMod L) ^ 2 = 0 :=
        hY2.symm.trans hY2_0
      have hLval : PadicInt.toZMod L = -c1 * (1 - a) * a⁻¹ := by
        field_simp [ha0, h1a]
        have h1' : c1 * (1 - a) + a * PadicInt.toZMod L = 0 := by
          have := congrArg (fun x => x * (1 - a)) h1
          field_simp [h1a] at this
          linear_combination this
        linear_combination h1'
      rw [hLval] at h2
      field_simp [ha0, h1a, h2ne] at h2
      linear_combination h2

/-- **Soundness of the `(1, 1)` sieve:** On the `(1, 1)` component where `L = 0`
(Teichmüller points), any common root of `p^2 * Y2 = 0` and `p^4 * Y4 = 0` satisfies
`c2 = 0 ∧ c4 = 0` modulo `p`. -/
theorem one_one_sieve_sound (p : ℕ) [Fact p.Prime] (c2 c4 : ZMod p)
    (Y2 Y4 : ℤ_[p])
    (hY2 : PadicInt.toZMod Y2 = c2) (hY4 : PadicInt.toZMod Y4 = c4)
    (h2 : (p : ℤ_[p]) ^ 2 * Y2 = 0) (h4 : (p : ℤ_[p]) ^ 4 * Y4 = 0) :
    c2 = 0 ∧ c4 = 0 := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := padicInt_p_ne_zero p
  have hY2_0 : Y2 = 0 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hp0)
  have hY4_0 : Y4 = 0 := (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 hp0)
  exact ⟨by rw [← hY2, hY2_0, map_zero], by rw [← hY4, hY4_0, map_zero]⟩

end BBPGrouping

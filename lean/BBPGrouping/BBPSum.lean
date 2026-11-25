module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-! # Prime-modulus BBP identities, binary carries, and fractional CRT -/

public section

namespace BBPGrouping

private theorem two_pow_half (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ^ (p / 2) = (ZMod.χ₈ (p : ZMod 8) : ZMod p) := by
  simpa [legendreSym.at_two hp] using (legendreSym.eq_pow p 2).symm

theorem bbp_prime_one (p k n : ℕ) (hp : p.Prime) (hpk : p = 8 * k + 1) (hn : 4 * k ≤ n) :
    (2 : ZMod p) ^ (n - 4 * k) = (2 : ZMod p) ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  have h := two_pow_half p (by omega)
  rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega), ite_eq_left (Or.inl (by omega)),
    show p / 2 = 4 * k by omega, Int.cast_one] at h
  calc
    _ = (2 : ZMod p) ^ (n - 4 * k) * 2 ^ (4 * k) := by rw [h, mul_one]
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hn]

theorem bbp_prime_five (p k n : ℕ) (hp : p.Prime) (hpk : p = 8 * k + 5) (hn : 4 * k ≤ n) :
    (2 : ZMod p) ^ (n - 4 * k) = -4 * (2 : ZMod p) ^ n := by
  let : Fact p.Prime := ⟨hp⟩
  have h := two_pow_half p (by omega)
  rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega), ite_eq_right (by omega),
    show p / 2 = 4 * k + 2 by omega, pow_add] at h
  have hfour : (2 : ZMod p) ^ (4 * k) * 4 = -1 := by
    norm_num at h
    exact h
  conv_rhs => rw [← Nat.sub_add_cancel hn, pow_add]
  linear_combination (2 : ZMod p) ^ (n - 4 * k) * hfour

theorem carry_identity (d n : ℕ) (hd : 0 < d) :
    (2 * ((2 : ℤ) ^ n % d) - (2 : ℤ) ^ (n + 1) % d) ∈ ({0, (d : ℤ)} : Set ℤ) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have h₀ := Int.emod_nonneg ((2 : ℤ) ^ n) hd'.ne'
  have h₁ := Int.emod_lt_of_pos ((2 : ℤ) ^ n) hd'
  let r := (2 : ℤ) ^ n % d
  have hpow : (2 : ℤ) ^ (n + 1) % d = (r + r) % d := by
    rw [pow_succ, mul_two, Int.add_emod]
  rw [hpow]
  change 2 * r - (r + r) % d = 0 ∨ 2 * r - (r + r) % d = d
  change 0 ≤ r at h₀
  change r < d at h₁
  by_cases h : r + r < d
  · left
    rw [Int.emod_eq_of_lt (by omega) h]
    omega
  · right
    rw [Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- Bézout coefficients give the two modular inverses and an integer correction. -/
theorem crt_fraction_decomposition (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hc : u.Coprime v) (a : ℤ) :
    ∃ v' u' z : ℤ, (v * v' ≡ 1 [ZMOD (u : ℤ)]) ∧ (u * u' ≡ 1 [ZMOD (v : ℤ)]) ∧
      (a : ℚ) / ((u : ℚ) * v) =
        (((a * v') % u : ℤ) : ℚ) / u + (((a * u') % v : ℤ) : ℚ) / v + z := by
  let u' := Nat.gcdA u v
  let v' := Nat.gcdB u v
  have hbez : (1 : ℤ) = u * u' + v * v' := by
    simpa [hc.gcd_eq_one, u', v'] using Nat.gcd_eq_gcd_ab u v
  refine ⟨v', u', (a * v') / u + (a * u') / v, ?_, ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨u', by linear_combination hbez⟩
  · exact Int.modEq_iff_dvd.mpr ⟨v', by linear_combination hbez⟩
  · have huq : (u : ℚ) ≠ 0 := by positivity
    have hvq : (v : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    exact_mod_cast (show a = _ from by
      push_cast
      linear_combination a * hbez - (v : ℤ) * Int.emod_add_ediv_mul (a * v') u -
        (u : ℤ) * Int.emod_add_ediv_mul (a * u') v)

end BBPGrouping

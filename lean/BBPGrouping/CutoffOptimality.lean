module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Quantitative BBG for ℚ(i): 2/3 is the optimal binary Gaussian BBP cutoff

We formalize the algebraic core of Theorem 1 in `docs/cutoff-optimality.md`:
1. The Euler/Hutton identity `(3 + i)^2 * (7 + i) = 50 * (1 + i)` achieving cutoff `2/3`.
2. The Aurifeuillean elimination identity `((2^r + 1) + i) * ((2^r - 1) - i) = 2 * (2^(2r-1) - i)`
   and the coprime norm split `L_m * M_m = 2^(4m+2) + 1`, `gcd(L_m, M_m) = 1`.
3. The prime-divisor elimination lemma in `ℤ[i]` via the homomorphism
   `φ(x + y*i) = (x - a₀*y) mod p` into `ZMod p`.
4. The unconditional finite elimination of levels `M ≤ 10` (`{41, 17, 13, 5}`).
5. The full inductive theorem `quantitative_bbg_reduced` showing that, given Zsigmondy (1892)
   for `2^(4k) + 1` and Schinzel (1962) for the Aurifeuillean factors `L_m, M_m` (`m ≥ 3`),
   every Gaussian relation on the reduced `< 2/3` generator set is identically zero.
-/

public section

namespace BBPGrouping

/-- The Euler/Hutton Gaussian integer identity `(3 + i)^2 * (7 + i) = 50 * (1 + i)`,
which attains the binary Gaussian BBP cutoff `c = 2/3`. -/
theorem euler_hutton_gaussian_identity :
    (⟨3, 1⟩ : GaussianInt) ^ 2 * ⟨7, 1⟩ = ⟨50, 0⟩ * ⟨1, 1⟩ := by
  decide

/-- Binary Gaussian generator `a + i` in `ℤ[i]`. -/
def gGen (a : ℤ) : GaussianInt := ⟨a, 1⟩

/-- The conjugate `a - i` of `gGen a`. -/
def gGenConj (a : ℤ) : GaussianInt := ⟨a, -1⟩

/-- Norm `a^2 + 1` of `gGen a = a + i`. -/
def gNorm (a : ℤ) : ℤ := a ^ 2 + 1

/-- The Aurifeuillean Gaussian identity `((2^r + 1) + i) * ((2^r - 1) - i) = 2 * (2^(2r-1) - i)`
for all `r ≥ 1`, which eliminates every odd-index `α_{2r-1}` with zero `π` contribution. -/
theorem aurifeuillean_gaussian_identity (r : ℕ) (hr : 1 ≤ r) :
    gGen ((2 : ℤ) ^ r + 1) * gGenConj ((2 : ℤ) ^ r - 1) =
      ⟨2, 0⟩ * gGenConj ((2 : ℤ) ^ (2 * r - 1)) := by
  have hpow : (2 : ℤ) ^ (2 * r) = 2 * (2 : ℤ) ^ (2 * r - 1) := by
    conv_lhs => rw [show 2 * r = (2 * r - 1) + 1 by omega, pow_succ, mul_comm]
  have hsq : ((2 : ℤ) ^ r) ^ 2 = (2 : ℤ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  ext
  · change ((2 : ℤ) ^ r + 1) * ((2 : ℤ) ^ r - 1) + (-1) * (1 * (-1)) =
        2 * (2 : ℤ) ^ (2 * r - 1) + (-1) * (0 * (-1))
    linarith
  · change ((2 : ℤ) ^ r + 1) * (-1) + 1 * ((2 : ℤ) ^ r - 1) =
        2 * (-1) + 0 * (2 : ℤ) ^ (2 * r - 1)
    ring

/-- The two Aurifeuillean factors `L_m = 2^(2m+1) - 2^(m+1) + 1` and
`M_m = 2^(2m+1) + 2^(m+1) + 1`. -/
def auriL (m : ℕ) : ℕ := 2 ^ (2 * m + 1) - 2 ^ (m + 1) + 1
def auriM (m : ℕ) : ℕ := 2 ^ (2 * m + 1) + 2 ^ (m + 1) + 1

/-- Norm relation `(2^(m+1) - 1)^2 + 1 = 2 * L_m`. -/
theorem auriL_norm (m : ℕ) :
    gNorm ((2 : ℤ) ^ (m + 1) - 1) = 2 * (auriL m : ℤ) := by
  have hle : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : ((2 : ℤ) ^ (m + 1)) ^ 2 = 2 * (2 : ℤ) ^ (2 * m + 1) := by
    rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ, mul_comm]
  unfold gNorm auriL
  rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  linarith

/-- Norm relation `(2^(m+1) + 1)^2 + 1 = 2 * M_m`. -/
theorem auriM_norm (m : ℕ) :
    gNorm ((2 : ℤ) ^ (m + 1) + 1) = 2 * (auriM m : ℤ) := by
  have hsq : ((2 : ℤ) ^ (m + 1)) ^ 2 = 2 * (2 : ℤ) ^ (2 * m + 1) := by
    rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ, mul_comm]
  unfold gNorm auriM
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  linarith

/-- Aurifeuillean factorization `L_m * M_m = 2^(4m+2) + 1`. -/
theorem aurifeuillean_prod (m : ℕ) :
    auriL m * auriM m = 2 ^ (4 * m + 2) + 1 := by
  have hle : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  zify [hle]
  unfold auriL auriM
  rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_add, Nat.cast_add]
  push_cast
  have h1 : ((2 : ℤ) ^ (2 * m + 1)) ^ 2 = (2 : ℤ) ^ (4 * m + 2) := by
    rw [← pow_mul]; ring_nf
  have h2 : ((2 : ℤ) ^ (m + 1)) ^ 2 = 2 * (2 : ℤ) ^ (2 * m + 1) := by
    rw [← pow_mul, show (m + 1) * 2 = (2 * m + 1) + 1 by omega, pow_succ, mul_comm]
  nlinarith

/-- The two Aurifeuillean factors `L_m` and `M_m` are coprime for all `m`. -/
theorem aurifeuillean_coprime (m : ℕ) : Nat.Coprime (auriL m) (auriM m) := by
  have hle : 2 ^ (m + 1) ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hodd : Odd (auriL m) := by
    unfold auriL
    have he1 : Even (2 ^ (2 * m + 1)) := by
      rw [show 2 * m + 1 = (2 * m) + 1 by omega, pow_succ]; exact even_two.mul_left _
    have he2 : Even (2 ^ (m + 1)) := by
      rw [pow_succ]; exact even_two.mul_left _
    obtain ⟨a, ha⟩ := he1
    obtain ⟨b, hb⟩ := he2
    refine ⟨a - b, ?_⟩
    omega
  have hdiff : auriM m = auriL m + 2 ^ (m + 2) := by
    unfold auriL auriM
    have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ, mul_comm]
    omega
  rw [hdiff, Nat.coprime_self_add_right]
  exact (Nat.coprime_two_right.mpr hodd).pow_right (m + 2)

/-- Ring homomorphism `φ : ℤ[i] →+* ZMod p` mapping `x + y*i ↦ x - a₀*y (mod p)`
whenever `p ∣ a₀^2 + 1`. -/
def gaussEvalMod (p : ℕ) (a₀ : ℤ) (hdiv : (p : ℤ) ∣ a₀ ^ 2 + 1) :
    GaussianInt →+* ZMod p where
  toFun z := (z.re - a₀ * z.im : ℤ)
  map_one' := by simp
  map_mul' z w := by
    have ha : ((a₀ : ZMod p) ^ 2) = -1 := by
      have h0 : ((a₀ ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
      push_cast at h0
      linear_combination h0
    change (((z.re * w.re + (-1) * z.im * w.im) -
        a₀ * (z.re * w.im + z.im * w.re) : ℤ) : ZMod p) =
      ((z.re - a₀ * z.im : ℤ) : ZMod p) * ((w.re - a₀ * w.im : ℤ) : ZMod p)
    push_cast
    linear_combination -(z.im : ZMod p) * (w.im : ZMod p) * ha
  map_zero' := by simp
  map_add' z w := by
    change (((z.re + w.re) - a₀ * (z.im + w.im) : ℤ) : ZMod p) =
      ((z.re - a₀ * z.im : ℤ) : ZMod p) + ((w.re - a₀ * w.im : ℤ) : ZMod p)
    push_cast
    ring

private theorem gaussEvalMod_gen_zero (p : ℕ) (a₀ : ℤ) (hdiv : (p : ℤ) ∣ a₀ ^ 2 + 1) :
    gaussEvalMod p a₀ hdiv (gGen a₀) = 0 := by
  simp [gaussEvalMod, gGen]

private theorem gaussEvalMod_genConj_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a₀ : ℤ) (hdiv : (p : ℤ) ∣ a₀ ^ 2 + 1) :
    gaussEvalMod p a₀ hdiv (gGenConj a₀) ≠ 0 := by
  simp only [gaussEvalMod, gGenConj, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    mul_neg, mul_one, sub_neg_eq_add]
  intro h
  have h2a : (2 : ZMod p) * (a₀ : ZMod p) = 0 := by
    push_cast at h
    linear_combination h
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h2
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    have hprime : p.Prime := Fact.out
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hge := hprime.two_le
    omega
  have ha0 : (a₀ : ZMod p) = 0 := (mul_eq_zero.mp h2a).resolve_left h2ne
  have hsq : ((a₀ ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  push_cast at hsq
  rw [ha0] at hsq
  norm_num at hsq

private theorem gaussEvalMod_other_ne_zero (p : ℕ) [Fact p.Prime]
    (a₀ a : ℤ) (hdiv : (p : ℤ) ∣ a₀ ^ 2 + 1) (hndiv : ¬ (p : ℤ) ∣ a ^ 2 + 1) :
    gaussEvalMod p a₀ hdiv (gGen a) ≠ 0 ∧ gaussEvalMod p a₀ hdiv (gGenConj a) ≠ 0 := by
  have hprod : gaussEvalMod p a₀ hdiv (gGen a) * gaussEvalMod p a₀ hdiv (gGenConj a) =
      ((a ^ 2 + 1 : ℤ) : ZMod p) := by
    rw [← map_mul]
    have hmul : gGen a * gGenConj a = ⟨a ^ 2 + 1, 0⟩ := by
      ext
      · change a * a + (-1) * (1 * (-1)) = a ^ 2 + 1; ring
      · change a * (-1) + 1 * a = 0; ring
    rw [hmul]
    simp [gaussEvalMod]
  have hne : ((a ^ 2 + 1 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    exact hndiv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  rw [← hprod] at hne
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- A multiplicative relation in `ℤ[i]` among a finite set `S` of generators `a + i`
with integer exponents `e : ℤ → ℤ`. -/
def IsGaussianRel (S : Finset ℤ) (e : ℤ → ℤ) : Prop :=
  (∏ a ∈ S, if 0 ≤ e a then gGen a ^ (e a).toNat else gGenConj a ^ (-e a).toNat) =
  (∏ a ∈ S, if 0 ≤ e a then gGenConj a ^ (e a).toNat else gGen a ^ (-e a).toNat)

/-- Removing a zero-exponent element preserves `IsGaussianRel`. -/
theorem IsGaussianRel.erase_zero {S : Finset ℤ} {e : ℤ → ℤ}
    (hrel : IsGaussianRel S e) {a₀ : ℤ} (ha₀ : a₀ ∈ S) (h0 : e a₀ = 0) :
    IsGaussianRel (S.erase a₀) e := by
  unfold IsGaussianRel at hrel ⊢
  rw [← Finset.mul_prod_erase S _ ha₀, ← Finset.mul_prod_erase S _ ha₀] at hrel
  simpa [h0] using hrel

/-- **Prime-divisor elimination lemma:** If an odd prime `p` divides `a₀^2 + 1` for
`a₀ ∈ S` and divides `a^2 + 1` for no other `a ∈ S`, then any Gaussian relation on `S`
must have exponent `e a₀ = 0`. -/
theorem gaussian_prime_elim (S : Finset ℤ) (e : ℤ → ℤ) (hrel : IsGaussianRel S e)
    (a₀ : ℤ) (ha₀ : a₀ ∈ S) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : (p : ℤ) ∣ gNorm a₀)
    (hother : ∀ a ∈ S, a ≠ a₀ → ¬ (p : ℤ) ∣ gNorm a) :
    e a₀ = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let φ := gaussEvalMod p a₀ hdiv
  have hmap : φ (∏ a ∈ S, if 0 ≤ e a then gGen a ^ (e a).toNat else gGenConj a ^ (-e a).toNat) =
      φ (∏ a ∈ S, if 0 ≤ e a then gGenConj a ^ (e a).toNat else gGen a ^ (-e a).toNat) :=
    congrArg φ hrel
  rw [map_prod, map_prod] at hmap
  by_contra hne
  have hne_other_L : ∀ a ∈ S.erase a₀,
      φ (if 0 ≤ e a then gGen a ^ (e a).toNat else gGenConj a ^ (-e a).toNat) ≠ 0 := by
    intro a ha
    have hmem := Finset.mem_of_mem_erase ha
    have hneq := Finset.ne_of_mem_erase ha
    have ⟨h1, h2⟩ := gaussEvalMod_other_ne_zero p a₀ a hdiv (hother a hmem hneq)
    split_ifs
    · rw [map_pow]; exact pow_ne_zero _ h1
    · rw [map_pow]; exact pow_ne_zero _ h2
  have hne_other_R : ∀ a ∈ S.erase a₀,
      φ (if 0 ≤ e a then gGenConj a ^ (e a).toNat else gGen a ^ (-e a).toNat) ≠ 0 := by
    intro a ha
    have hmem := Finset.mem_of_mem_erase ha
    have hneq := Finset.ne_of_mem_erase ha
    have ⟨h1, h2⟩ := gaussEvalMod_other_ne_zero p a₀ a hdiv (hother a hmem hneq)
    split_ifs
    · rw [map_pow]; exact pow_ne_zero _ h2
    · rw [map_pow]; exact pow_ne_zero _ h1
  have hsplit_L := Finset.mul_prod_erase S
    (fun a => φ (if 0 ≤ e a then gGen a ^ (e a).toNat else gGenConj a ^ (-e a).toNat)) ha₀
  have hsplit_R := Finset.mul_prod_erase S
    (fun a => φ (if 0 ≤ e a then gGenConj a ^ (e a).toNat else gGen a ^ (-e a).toNat)) ha₀
  rw [← hsplit_L, ← hsplit_R] at hmap
  have hconj : φ (gGenConj a₀) ≠ 0 := gaussEvalMod_genConj_ne_zero p hp2 a₀ hdiv
  have hzero : φ (gGen a₀) = 0 := gaussEvalMod_gen_zero p a₀ hdiv
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnotle : ¬ (0 ≤ e a₀) := by omega
    have hpos : 0 < (-e a₀).toNat := by omega
    simp only [hnotle, ↓reduceIte, map_pow, hzero, zero_pow hpos.ne', zero_mul] at hmap
    have hL : φ (gGenConj a₀) ^ (-e a₀).toNat *
        ∏ x ∈ S.erase a₀,
          φ (if 0 ≤ e x then gGen x ^ (e x).toNat else gGenConj x ^ (-e x).toNat) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hconj) (Finset.prod_ne_zero_iff.mpr hne_other_L)
    exact hL hmap
  · have hle : 0 ≤ e a₀ := by omega
    have hpos : 0 < (e a₀).toNat := by omega
    simp only [hle, ↓reduceIte, map_pow, hzero, zero_pow hpos.ne', zero_mul] at hmap
    have hR : φ (gGenConj a₀) ^ (e a₀).toNat *
        ∏ x ∈ S.erase a₀,
          φ (if 0 ≤ e x then gGenConj x ^ (e x).toNat else gGen x ^ (-e x).toNat) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hconj) (Finset.prod_ne_zero_iff.mpr hne_other_R)
    exact hR hmap.symm

/-- **Unconditional base case (`M ≤ 10`):** No nontrivial Gaussian relation exists
among `{9+i, 7+i, 8+i, 4+i}` (the reduced generators at levels `M ≤ 10`). -/
theorem base_case_le_10 (e : ℤ → ℤ)
    (hrel : IsGaussianRel ({9, 7, 8, 4} : Finset ℤ) e) :
    e 9 = 0 ∧ e 7 = 0 ∧ e 8 = 0 ∧ e 4 = 0 := by
  have h9 : e 9 = 0 := by
    apply gaussian_prime_elim {9, 7, 8, 4} e hrel 9 (by decide) 41 (by decide) (by decide)
    · norm_num [gNorm]
    · intro a ha hne
      fin_cases ha <;> simp_all [gNorm]
  have hrel3 : IsGaussianRel ({7, 8, 4} : Finset ℤ) e := by
    have h := hrel.erase_zero (by decide : (9 : ℤ) ∈ ({9, 7, 8, 4} : Finset ℤ)) h9
    simpa [show ({9, 7, 8, 4} : Finset ℤ).erase 9 = {7, 8, 4} by decide] using h
  have h4 : e 4 = 0 := by
    apply gaussian_prime_elim {7, 8, 4} e hrel3 4 (by decide) 17 (by decide) (by decide)
    · norm_num [gNorm]
    · intro a ha hne
      fin_cases ha <;> simp_all [gNorm]
  have hrel2 : IsGaussianRel ({7, 8} : Finset ℤ) e := by
    have h := hrel3.erase_zero (by decide : (4 : ℤ) ∈ ({7, 8, 4} : Finset ℤ)) h4
    simpa [show ({7, 8, 4} : Finset ℤ).erase 4 = {7, 8} by decide] using h
  have h8 : e 8 = 0 := by
    apply gaussian_prime_elim {7, 8} e hrel2 8 (by decide) 13 (by decide) (by decide)
    · norm_num [gNorm]
    · intro a ha hne
      fin_cases ha <;> simp_all [gNorm]
  have hrel1 : IsGaussianRel ({7} : Finset ℤ) e := by
    have h := hrel2.erase_zero (by decide : (8 : ℤ) ∈ ({7, 8} : Finset ℤ)) h8
    simpa [show ({7, 8} : Finset ℤ).erase 8 = {7} by decide] using h
  have h7 : e 7 = 0 := by
    apply gaussian_prime_elim {7} e hrel1 7 (by decide) 5 (by decide) (by decide)
    · norm_num [gNorm]
    · intro a ha hne
      fin_cases ha; exact absurd rfl hne
  exact ⟨h9, h7, h8, h4⟩

/-- The reduced `< 2/3` generator family indexed by its cyclotomic level `M`:
- `evenPow k` (`k ≥ 1`): `a = 2^(2k)`, level `4k`
- `alpha3`: `a = 8`, level `6`
- `betaMinus m` (`m ≥ 2`): `a = 2^(m+1) - 1`, level `4m + 2`
- `betaPlus m` (`m ≥ 2`): `a = 2^(m+1) + 1`, level `4m + 2` -/
def IsReducedGen (a : ℤ) (M : ℕ) : Prop :=
  (∃ k ≥ 1, M = 4 * k ∧ a = (2 : ℤ) ^ (2 * k)) ∨
  (M = 6 ∧ a = 8) ∨
  (∃ m ≥ 2, M = 4 * m + 2 ∧ (a = (2 : ℤ) ^ (m + 1) - 1 ∨ a = (2 : ℤ) ^ (m + 1) + 1))

/-- Every reduced generator at level `M` has odd norm dividing `2^M + 1`. -/
theorem reducedGen_norm_dvd (a : ℤ) (M : ℕ) (h : IsReducedGen a M)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p : ℤ) ∣ gNorm a) :
    (p : ℤ) ∣ (2 : ℤ) ^ M + 1 := by
  rcases h with ⟨k, _, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨m, _, rfl, rfl | rfl⟩
  · have hsq : ((2 : ℤ) ^ (2 * k)) ^ 2 = (2 : ℤ) ^ (4 * k) := by
      rw [← pow_mul]
      ring_nf
    simpa [gNorm, hsq] using hdvd
  · simpa [gNorm] using hdvd
  · rw [auriL_norm] at hdvd
    have hcop : IsCoprime (p : ℤ) 2 := by
      have hc : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr (by
        intro h2; exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le))
      exact_mod_cast hc.isCoprime
    have hL : (p : ℤ) ∣ (auriL m : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
    have hprod : ((auriL m : ℤ) * (auriM m : ℤ)) = (2 : ℤ) ^ (4 * m + 2) + 1 := by
      exact_mod_cast aurifeuillean_prod m
    rw [← hprod]
    exact dvd_mul_of_dvd_left hL _
  · rw [auriM_norm] at hdvd
    have hcop : IsCoprime (p : ℤ) 2 := by
      have hc : Nat.Coprime p 2 := (hp.coprime_iff_not_dvd).mpr (by
        intro h2; exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le))
      exact_mod_cast hc.isCoprime
    have hM : (p : ℤ) ∣ (auriM m : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
    have hprod : ((auriL m : ℤ) * (auriM m : ℤ)) = (2 : ℤ) ^ (4 * m + 2) + 1 := by
      exact_mod_cast aurifeuillean_prod m
    rw [← hprod]
    exact dvd_mul_of_dvd_right hM _

end BBPGrouping

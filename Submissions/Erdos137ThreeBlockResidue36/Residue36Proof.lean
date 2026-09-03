import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős 137: residue condition for powerful products of three consecutive integers

If the product of three consecutive positive integers is powerful, every prime
dividing the product divides it at least squared.  For `p = 2` and `p = 3` this
is a pure congruence computation:

* the block `{s+1, s+2, s+3}` has 2-adic valuation exactly `1` when `s ≡ 0 [MOD 4]`
  (a single even element, congruent to `2` modulo `4`), so a powerful product
  forces `s ≢ 0 [MOD 4]`;
* exactly one element of the block is divisible by `3`, so 3-adic valuation
  at least `2` forces that element to be divisible by `9`, i.e. `s ≡ 6, 7` or
  `8 [MOD 9]`.

Combining both by CRT leaves nine residues modulo `36` for the first element.
-/

namespace Submissions.Erdos137ThreeBlockResidue36.Residue36Proof

open Finset
open scoped BigOperators

def Powerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

def consecutiveProduct (start length : ℕ) : ℕ :=
  ∏ x ∈ Finset.Ioc start (start + length), x

theorem prod_three (s : ℕ) : consecutiveProduct s 3 = (s + 1) * (s + 2) * (s + 3) := by
  unfold consecutiveProduct
  rw [Finset.prod_Ioc_succ_top (show s ≤ s + 2 by omega) (fun x => x),
      Finset.prod_Ioc_succ_top (show s ≤ s + 1 by omega) (fun x => x),
      Finset.prod_Ioc_succ_top (show s ≤ s by omega) (fun x => x),
      Finset.Ioc_eq_empty (by omega)]
  simp [Finset.prod_empty, one_mul]

theorem two_dvd_prod3 (s : ℕ) : (2 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3) := by
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · have h2 : (2 : ℕ) ∣ s + 2 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 (s + 1)) (s + 3)
  · have h2 : (2 : ℕ) ∣ s + 1 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 (s + 2)) (s + 3)

theorem three_dvd_prod3 (s : ℕ) : (3 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3) := by
  have hcase : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hcase with h | h | h
  · have h3 : (3 : ℕ) ∣ s + 3 := by omega
    exact dvd_mul_of_dvd_right h3 ((s + 1) * (s + 2))
  · have h3 : (3 : ℕ) ∣ s + 2 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3 (s + 1)) (s + 3)
  · have h3 : (3 : ℕ) ∣ s + 1 := by omega
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h3 (s + 2)) (s + 3)

-- if a 3-block product is powerful then 4 and 9 divide it
theorem powerful_3block_imp (s : ℕ) (hP : Powerful (consecutiveProduct s 3)) :
    (4 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3) ∧ (9 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3) := by
  rw [prod_three s] at hP
  exact ⟨hP 2 Nat.prime_two (two_dvd_prod3 s), hP 3 Nat.prime_three (three_dvd_prod3 s)⟩

-- the product is congruent modulo m to the product of shifted residues
theorem prod3_modeq (s m : ℕ) :
    (s % m + 1) * (s % m + 2) * (s % m + 3) ≡ (s + 1) * (s + 2) * (s + 3) [MOD m] :=
  (((Nat.mod_modEq s m).add_right 1).mul ((Nat.mod_modEq s m).add_right 2)).mul
    ((Nat.mod_modEq s m).add_right 3)

-- mod 4: 4 | product forces s % 4 ≠ 0
theorem four_dvd_imp (s : ℕ) (h : (4 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3)) : s % 4 ≠ 0 := by
  intro hcontra
  have hmod : (s + 1) * (s + 2) * (s + 3) % 4 = (s % 4 + 1) * (s % 4 + 2) * (s % 4 + 3) % 4 :=
    (prod3_modeq s 4).symm
  rw [hcontra] at hmod
  have hval : (0 + 1) * (0 + 2) * (0 + 3) % 4 = 2 := by decide
  omega

-- mod 9: 9 | product forces s % 9 ∈ {6, 7, 8}
theorem nine_dvd_imp (s : ℕ) (h : (9 : ℕ) ∣ (s + 1) * (s + 2) * (s + 3)) :
    s % 9 = 6 ∨ s % 9 = 7 ∨ s % 9 = 8 := by
  have key : ∀ k : Fin 9, ((k : ℕ) + 1) * ((k : ℕ) + 2) * ((k : ℕ) + 3) % 9 = 0 ↔
      ((k : ℕ) = 6 ∨ (k : ℕ) = 7 ∨ (k : ℕ) = 8) := by decide
  have hlt : s % 9 < 9 := Nat.mod_lt s (show 0 < 9 by decide)
  have hmod : (s + 1) * (s + 2) * (s + 3) % 9 = (s % 9 + 1) * (s % 9 + 2) * (s % 9 + 3) % 9 :=
    (prod3_modeq s 9).symm
  have hzero : (s % 9 + 1) * (s % 9 + 2) * (s % 9 + 3) % 9 = 0 := by omega
  rcases (key ⟨s % 9, hlt⟩).mp hzero with h | h | h
  · simp at h; omega
  · simp at h; omega
  · simp at h; omega

theorem proof : ∀ s : ℕ, Powerful (consecutiveProduct s 3) →
    (s + 1) % 36 = 0 ∨ (s + 1) % 36 = 7 ∨ (s + 1) % 36 = 8 ∨
    (s + 1) % 36 = 16 ∨ (s + 1) % 36 = 18 ∨ (s + 1) % 36 = 26 ∨
    (s + 1) % 36 = 27 ∨ (s + 1) % 36 = 34 ∨ (s + 1) % 36 = 35 := by
  intro s hP
  obtain ⟨h4, h9⟩ := powerful_3block_imp s hP
  have hs4 : s % 4 ≠ 0 := four_dvd_imp s h4
  have hs9 : s % 9 = 6 ∨ s % 9 = 7 ∨ s % 9 = 8 := nine_dvd_imp s h9
  have hm4 : ((s + 1) % 36) % 4 = (s + 1) % 4 :=
    Nat.mod_mod_of_dvd (s + 1) (show (4 : ℕ) ∣ 36 by decide)
  have hm9 : ((s + 1) % 36) % 9 = (s + 1) % 9 :=
    Nat.mod_mod_of_dvd (s + 1) (show (9 : ℕ) ∣ 36 by decide)
  have key : ∀ k : Fin 36,
      ((k : ℕ) % 4 ≠ 1 ∧ ((k : ℕ) % 9 = 0 ∨ (k : ℕ) % 9 = 7 ∨ (k : ℕ) % 9 = 8)) →
      ((k : ℕ) = 0 ∨ (k : ℕ) = 7 ∨ (k : ℕ) = 8 ∨ (k : ℕ) = 16 ∨ (k : ℕ) = 18 ∨
       (k : ℕ) = 26 ∨ (k : ℕ) = 27 ∨ (k : ℕ) = 34 ∨ (k : ℕ) = 35) := by decide
  refine (key ⟨(s + 1) % 36, Nat.mod_lt (s + 1) (show 0 < 36 by decide)⟩) ⟨?_, ?_⟩
  · show (s + 1) % 36 % 4 ≠ 1
    omega
  · show (s + 1) % 36 % 9 = 0 ∨ (s + 1) % 36 % 9 = 7 ∨ (s + 1) % 36 % 9 = 8
    omega

end Submissions.Erdos137ThreeBlockResidue36.Residue36Proof

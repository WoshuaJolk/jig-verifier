import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos1135ShortOddCycles.ShortCycles

set_option maxHeartbeats 1000000

private theorem pow_two_mono {i j : ℕ} (h : i ≤ j) : 2 ^ i ≤ 2 ^ j :=
  Nat.pow_le_pow_right (by decide) h

/-- The next odd value after one is one. -/
private theorem after_one (b k : ℕ) (hb : 0 < b) (ob : Odd b)
    (hk : 0 < k) (h : 4 = 2 ^ k * b) : b = 1 := by
  have hp : 2 ≤ 2 ^ k := by simpa using pow_two_mono hk
  have hmul := Nat.mul_le_mul_right b hp
  have hb_bound : b ≤ 2 := by nlinarith
  rcases ob with ⟨t, ht⟩
  omega

/-- At a nontrivial minimum, the first odd transition has exactly one halving. -/
private theorem first_exponent (a b k : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hk : 0 < k) (h : 3 * a + 1 = 2 ^ k * b) : k = 1 := by
  by_contra hne
  have hk2 : 2 ≤ k := by omega
  have hp : 4 ≤ 2 ^ k := by simpa using pow_two_mono hk2
  have hmul := Nat.mul_le_mul_right b hp
  nlinarith

private theorem two_minimum (a b k l : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (hk : 0 < k) (hl : 0 < l)
    (h1 : 3 * a + 1 = 2 ^ k * b) (h2 : 3 * b + 1 = 2 ^ l * a) : a = 1 := by
  by_contra hne
  have ha2 : 2 ≤ a := by omega
  have hk1 := first_exponent a b k ha2 hab hk h1
  subst k
  norm_num at h1
  by_cases hl2 : l ≤ 2
  · have hp : 2 ^ l ≤ 4 := by simpa using pow_two_mono hl2
    have hmul := Nat.mul_le_mul_right a hp
    nlinarith
  · have hl3 : 3 ≤ l := by omega
    have hp : 8 ≤ 2 ^ l := by simpa using pow_two_mono hl3
    have hmul := Nat.mul_le_mul_right a hp
    nlinarith

private theorem two_cycle (a b k l : ℕ) (ha : 0 < a) (hb : 0 < b)
    (oa : Odd a) (ob : Odd b) (hk : 0 < k) (hl : 0 < l)
    (h1 : 3 * a + 1 = 2 ^ k * b) (h2 : 3 * b + 1 = 2 ^ l * a) :
    a = 1 ∧ b = 1 := by
  rcases le_total a b with hab | hba
  · have ha1 := two_minimum a b k l ha hab hk hl h1 h2
    have hb1 := after_one b k hb ob hk (by simpa [ha1] using h1)
    exact ⟨ha1, hb1⟩
  · have hb1 := two_minimum b a l k hb hba hl hk h2 h1
    have ha1 := after_one a l ha oa hl (by simpa [hb1] using h2)
    exact ⟨ha1, hb1⟩

private theorem three_minimum (a b c k l m : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hac : a ≤ c) (hk : 0 < k) (hl : 0 < l) (hm : 0 < m)
    (h1 : 3 * a + 1 = 2 ^ k * b) (h2 : 3 * b + 1 = 2 ^ l * c)
    (h3 : 3 * c + 1 = 2 ^ m * a) : a = 1 := by
  by_contra hne
  have ha2 : 2 ≤ a := by omega
  have hk1 := first_exponent a b k ha2 hab hk h1
  subst k
  norm_num at h1
  have hl_bound : l ≤ 2 := by
    by_contra hlarge
    have hl3 : 3 ≤ l := by omega
    have hp : 8 ≤ 2 ^ l := by simpa using pow_two_mono hl3
    have hmul := Nat.mul_le_mul_right c hp
    nlinarith
  interval_cases l
  · norm_num at h2
    have hm_low : 3 ≤ m := by
      by_contra hsmall
      have hle : m ≤ 2 := by omega
      have hp : 2 ^ m ≤ 4 := by simpa using pow_two_mono hle
      have hmul := Nat.mul_le_mul_right a hp
      nlinarith
    have hm_high : m ≤ 3 := by
      by_contra hlarge
      have hle : 4 ≤ m := by omega
      have hp : 16 ≤ 2 ^ m := by simpa using pow_two_mono hle
      have hmul := Nat.mul_le_mul_right a hp
      nlinarith
    have hm3 : m = 3 := by omega
    subst m
    norm_num at h3
    omega
  · norm_num at h2
    have hm_low : 2 ≤ m := by
      by_contra hsmall
      have hle : m ≤ 1 := by omega
      have hp : 2 ^ m ≤ 2 := by simpa using pow_two_mono hle
      have hmul := Nat.mul_le_mul_right a hp
      nlinarith
    have hm_high : m ≤ 2 := by
      by_contra hlarge
      have hle : 3 ≤ m := by omega
      have hp : 8 ≤ 2 ^ m := by simpa using pow_two_mono hle
      have hmul := Nat.mul_le_mul_right a hp
      nlinarith
    have hm2 : m = 2 := by omega
    subst m
    norm_num at h3
    omega

private theorem three_cycle (a b c k l m : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (oa : Odd a) (ob : Odd b) (oc : Odd c)
    (hk : 0 < k) (hl : 0 < l) (hm : 0 < m)
    (h1 : 3 * a + 1 = 2 ^ k * b) (h2 : 3 * b + 1 = 2 ^ l * c)
    (h3 : 3 * c + 1 = 2 ^ m * a) : a = 1 ∧ b = 1 ∧ c = 1 := by
  have hsome : a = 1 ∨ b = 1 ∨ c = 1 := by
    by_cases hab : a ≤ b
    · by_cases hac : a ≤ c
      · exact Or.inl (three_minimum a b c k l m ha hab hac hk hl hm h1 h2 h3)
      · exact Or.inr (Or.inr (three_minimum c a b m k l hc (by omega) (by omega)
          hm hk hl h3 h1 h2))
    · by_cases hbc : b ≤ c
      · exact Or.inr (Or.inl (three_minimum b c a l m k hb hbc (by omega)
          hl hm hk h2 h3 h1))
      · exact Or.inr (Or.inr (three_minimum c a b m k l hc (by omega) (by omega)
          hm hk hl h3 h1 h2))
  rcases hsome with ha1 | hb1 | hc1
  · have hb1 := after_one b k hb ob hk (by simpa [ha1] using h1)
    have hc1 := after_one c l hc oc hl (by simpa [hb1] using h2)
    exact ⟨ha1, hb1, hc1⟩
  · have hc1 := after_one c l hc oc hl (by simpa [hb1] using h2)
    have ha1 := after_one a m ha oa hm (by simpa [hc1] using h3)
    exact ⟨ha1, hb1, hc1⟩
  · have ha1 := after_one a m ha oa hm (by simpa [hc1] using h3)
    have hb1 := after_one b k hb ob hk (by simpa [ha1] using h1)
    exact ⟨ha1, hb1, hc1⟩

/-- Closing after two or three odd transitions forces the trivial cycle.
A one-transition loop is included by repeating its odd value. -/
theorem proof :
    ∀ a b c k l m : ℕ, 0 < a → 0 < b → 0 < c →
      Odd a → Odd b → Odd c → 0 < k → 0 < l → 0 < m →
      3 * a + 1 = 2 ^ k * b → 3 * b + 1 = 2 ^ l * c →
      (c = a ∨ 3 * c + 1 = 2 ^ m * a) → a = 1 ∧ b = 1 ∧ c = 1 := by
  intro a b c k l m ha hb hc oa ob oc hk hl hm h1 h2 hclose
  rcases hclose with hca | h3
  · have h2' : 3 * b + 1 = 2 ^ l * a := by simpa [hca] using h2
    have hp := two_cycle a b k l ha hb oa ob hk hl h1 h2'
    exact ⟨hp.1, hp.2, hca.trans hp.1⟩
  · exact three_cycle a b c k l m ha hb hc oa ob oc hk hl hm h1 h2 h3

/-- The hypotheses hold for the genuine trivial orbit. -/
theorem nonvacuity :
    (0 : ℕ) < 1 ∧ Odd (1 : ℕ) ∧ (0 : ℕ) < 2 ∧
      3 * (1 : ℕ) + 1 = 2 ^ 2 * 1 := by norm_num

/-- An actual finite path is not silently promoted to a closed orbit. -/
theorem open_path_control :
    3 * (3 : ℕ) + 1 = 2 ^ 1 * 5 ∧ 3 * (5 : ℕ) + 1 = 2 ^ 4 * 1 ∧
      ¬ ((1 : ℕ) = 3 ∨ 3 * 1 + 1 = 2 ^ 2 * 3) := by norm_num

end Submissions.Erdos1135ShortOddCycles.ShortCycles

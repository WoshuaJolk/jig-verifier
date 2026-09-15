import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Submissions.ErdosStrausShiftObstruction409577.ShiftObstruction

set_option maxHeartbeats 2000000

/-- Symmetry makes the smaller factor an effective search parameter. -/
theorem ordered_bound (n a b m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (hab : a ≤ b) (h : n + a + b = 4 * a * b * m) :
    4 * a * a * m ≤ n + 2 * a := by
  zify at ha hm hab h ⊢
  have hcoef : (0 : ℤ) ≤ 4 * (a : ℤ) * (m : ℤ) - 1 := by
    nlinarith [mul_pos ha hm]
  nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hab)]

theorem no_ordered_409 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hab : a ≤ b)
    (h : 409 + a + b = 4 * a * b * m) : False := by
  have hbound := ordered_bound 409 a b m ha hm hab h
  have hquad : 4 * a * a ≤ 409 + 2 * a := by
    have hprod := Nat.mul_le_mul_left (4 * a * a) hm
    nlinarith
  have ha_bound : a ≤ 10 := by
    by_contra hlarge
    have hmin : 11 ≤ a := by omega
    have hmul := Nat.mul_le_mul_left a hmin
    nlinarith
  interval_cases a
  · have hm_bound : m ≤ 102 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 25 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 11 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 6 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 4 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 2 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 2 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega

theorem no_equation_409 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (h : 409 + a + b = 4 * a * b * m) : False := by
  rcases le_total a b with hab | hba
  · exact no_ordered_409 a b m ha hb hm hab h
  · exact no_ordered_409 b a m hb ha hm hba (by nlinarith [h])

theorem no_ordered_577 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hab : a ≤ b)
    (h : 577 + a + b = 4 * a * b * m) : False := by
  have hbound := ordered_bound 577 a b m ha hm hab h
  have hquad : 4 * a * a ≤ 577 + 2 * a := by
    have hprod := Nat.mul_le_mul_left (4 * a * a) hm
    nlinarith
  have ha_bound : a ≤ 12 := by
    by_contra hlarge
    have hmin : 13 ≤ a := by omega
    have hmul := Nat.mul_le_mul_left a hmin
    nlinarith
  interval_cases a
  · have hm_bound : m ≤ 144 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 36 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 16 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 9 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 5 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 4 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 3 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 2 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega
  · have hm_bound : m ≤ 1 := by omega
    interval_cases m <;> omega

theorem no_equation_577 (a b m : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (h : 577 + a + b = 4 * a * b * m) : False := by
  rcases le_total a b with hab | hba
  · exact no_ordered_577 a b m ha hb hm hab h
  · exact no_ordered_577 b a m hb ha hm hba (by nlinarith [h])

theorem proof :
    ∀ n : ℕ, (n = 409 ∨ n = 577) →
      ∀ a b g m : ℕ, 0 < a → 0 < b → 0 < m →
        n + a = b * g → g + 1 ≠ 4 * a * m := by
  intro n hn a b g m ha hb hm hbg hg
  have heq := congrArg (fun t : ℕ => b * t) hg
  have hcore : n + a + b = 4 * a * b * m := by nlinarith [heq]
  rcases hn with rfl | rfl
  · exact no_equation_409 a b m ha hb hm hcore
  · exact no_equation_577 a b m ha hb hm hcore

end Submissions.ErdosStrausShiftObstruction409577.ShiftObstruction

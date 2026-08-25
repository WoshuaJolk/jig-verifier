import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos141FirstFive.Worker09Direct

theorem proof :
    Nat.Prime 9843019 ∧
    Nat.Prime 9843049 ∧
    Nat.Prime 9843079 ∧
    Nat.Prime 9843109 ∧
    Nat.Prime 9843139 ∧
    9843019 + 30 = 9843049 ∧
    9843049 + 30 = 9843079 ∧
    9843079 + 30 = 9843109 ∧
    9843109 + 30 = 9843139 ∧
    ∀ p : ℕ, 9843019 ≤ p → p ≤ 9843139 →
      (Nat.Prime p ↔
        p = 9843019 ∨ p = 9843049 ∨ p = 9843079 ∨
        p = 9843109 ∨ p = 9843139) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · intro p hp hP
    interval_cases p <;> norm_num

end Submissions.Erdos141FirstFive.Worker09Direct

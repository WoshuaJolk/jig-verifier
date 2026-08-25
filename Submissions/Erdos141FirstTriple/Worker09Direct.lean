import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos141FirstTriple.Worker09Direct

theorem proof :
    Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
    3 + 2 = 5 ∧ 5 + 2 = 7 ∧
    ∀ p : ℕ, 3 ≤ p → p ≤ 7 →
      (Nat.Prime p ↔ p = 3 ∨ p = 5 ∨ p = 7) := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, ?_⟩
  intro p hlo hhi
  interval_cases p <;> norm_num

end Submissions.Erdos141FirstTriple.Worker09Direct

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos141FirstFour.Worker09Direct

theorem proof :
    Nat.Prime 251 ∧ Nat.Prime 257 ∧ Nat.Prime 263 ∧ Nat.Prime 269 ∧
    251 + 6 = 257 ∧ 257 + 6 = 263 ∧ 263 + 6 = 269 ∧
    ∀ p : ℕ, 251 ≤ p → p ≤ 269 →
      (Nat.Prime p ↔ p = 251 ∨ p = 257 ∨ p = 263 ∨ p = 269) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, rfl, rfl, rfl, ?_⟩
  intro p hlo hhi
  interval_cases p <;> norm_num [Nat.prime_def] at *

end Submissions.Erdos141FirstFour.Worker09Direct

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos203FiniteBoxWitness.Direct

theorem proof :
    Nat.Coprime 427771 6 ∧
      ∀ k ≤ 8, ∀ l ≤ 8,
        ¬(2 ^ k * 3 ^ l * 427771 + 1).Prime := by
  constructor
  · norm_num [Nat.Coprime]
  · intro k hk l hl
    interval_cases k <;> interval_cases l <;> norm_num [Nat.prime_def_lt]

end Submissions.Erdos203FiniteBoxWitness.Direct

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Nat

namespace Submissions.Erdos396BaseCases.Direct

theorem proof :
    ∀ k : ℕ, k ≤ 1 → ∃ n : ℕ, descFactorial n (k + 1) ∣ centralBinom n := by
  intro k hk
  interval_cases k
  · exact ⟨1, by norm_num [descFactorial, centralBinom]⟩
  · exact ⟨2, by decide⟩

end Submissions.Erdos396BaseCases.Direct

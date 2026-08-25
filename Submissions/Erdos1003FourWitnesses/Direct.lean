import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1003FourWitnesses.Direct

theorem proof :
    ∀ n ∈ ({1, 3, 15, 104} : Finset ℕ),
      Nat.totient n = Nat.totient (n + 1) := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide

end Submissions.Erdos1003FourWitnesses.Direct

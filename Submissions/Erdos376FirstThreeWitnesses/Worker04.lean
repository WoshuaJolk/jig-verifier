import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

namespace Submissions.Erdos376FirstThreeWitnesses.Worker04

theorem proof :
    ∀ n ∈ ({0, 1, 10} : Finset ℕ), n.centralBinom.Coprime 105 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · norm_num
  · decide
  · decide

end Submissions.Erdos376FirstThreeWitnesses.Worker04

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos282OddUnitFractionFirstStep.Direct

theorem proof :
    ∀ n : ℕ, 1 < n → Odd n →
      let chosen :=
        sInf {m : ℕ | Odd m ∧ (1 : ℚ) / (1 / (n : ℚ)) ≤ m}
      chosen = n ∧ (1 / (n : ℚ)) - 1 / (chosen : ℚ) = 0 := by
  intro n hn hodd
  have hleast : IsLeast {m : ℕ | Odd m ∧ n ≤ m} n := by
    exact ⟨⟨hodd, le_rfl⟩, fun _ hm => hm.2⟩
  have hsinf : sInf {m : ℕ | Odd m ∧ n ≤ m} = n :=
    IsLeast.csInf_eq hleast
  simp [hsinf]

end Submissions.Erdos282OddUnitFractionFirstStep.Direct

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Submissions.Erdos483OneColorBoundary.Explicit

def ForcesSchur (colors N : ℕ) : Prop :=
  ∀ coloring : ℕ → Fin colors,
    ∃ a b c : ℕ,
      1 ≤ a ∧ a ≤ N ∧
      1 ≤ b ∧ b ≤ N ∧
      1 ≤ c ∧ c ≤ N ∧
      a + b = c ∧
      coloring a = coloring b ∧ coloring b = coloring c

theorem proof : ForcesSchur 1 2 := by
  intro coloring
  refine ⟨1, 1, 2, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, ?_, ?_⟩ <;> apply Subsingleton.elim

end Submissions.Erdos483OneColorBoundary.Explicit

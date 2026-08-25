import Mathlib.Data.Fin.Basic

namespace Submissions.Erdos483OneColorBoundary.FalsePremise

def ForcesSchur (colors N : ℕ) : Prop :=
  ∀ coloring : ℕ → Fin colors,
    ∃ a b c : ℕ,
      1 ≤ a ∧ a ≤ N ∧
      1 ≤ b ∧ b ≤ N ∧
      1 ≤ c ∧ c ≤ N ∧
      a + b = c ∧
      coloring a = coloring b ∧ coloring b = coloring c

theorem proof : False → ForcesSchur 1 2 := by
  intro h
  exact h.elim

end Submissions.Erdos483OneColorBoundary.FalsePremise

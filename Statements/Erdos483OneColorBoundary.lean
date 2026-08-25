import Mathlib.Data.Fin.Basic

namespace Statements.Erdos483OneColorBoundary

def ForcesSchur (colors N : ℕ) : Prop :=
  ∀ coloring : ℕ → Fin colors,
    ∃ a b c : ℕ,
      1 ≤ a ∧ a ≤ N ∧
      1 ≤ b ∧ b ≤ N ∧
      1 ≤ c ∧ c ≤ N ∧
      a + b = c ∧
      coloring a = coloring b ∧ coloring b = coloring c

abbrev statement : Prop := ForcesSchur 1 2

theorem target : statement := sorry

end Statements.Erdos483OneColorBoundary

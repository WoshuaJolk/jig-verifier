import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat

namespace Statements.Erdos548ErdosSosTree

open SimpleGraph

/-- Erdős Problem 548 (the Erdős–Sós conjecture): for `n ≥ k + 1`, every graph on
`n` vertices with at least `(k - 1) / 2 · n + 1` edges contains every tree on
`k + 1` vertices. -/
abbrev statement : Prop :=
  ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
      ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G

theorem target : statement := sorry

end Statements.Erdos548ErdosSosTree

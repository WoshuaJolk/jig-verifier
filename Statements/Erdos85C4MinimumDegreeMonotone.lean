import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos85C4MinimumDegreeMonotone

open Classical Filter Finset SimpleGraph
open scoped SimpleGraph

/-- The least minimum-degree threshold forcing a four-cycle on `n` vertices. -/
noncomputable def c4Threshold (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)), G.minDegree ≥ k → (cycleGraph 4) ⊑ G}

/-- Erdős Problem 85: the four-cycle minimum-degree threshold is eventually nondecreasing. -/
abbrev statement : Prop :=
  ∀ᶠ n in Filter.atTop, c4Threshold n ≤ c4Threshold (n + 1)

theorem target : statement := sorry

end Statements.Erdos85C4MinimumDegreeMonotone

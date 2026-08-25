import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Statements.Erdos85ThresholdUpperStep

open Finset SimpleGraph
open scoped Classical SimpleGraph

/-- The least minimum-degree threshold forcing a four-cycle on `n` vertices. -/
noncomputable def c4Threshold (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)), G.minDegree ≥ k → (cycleGraph 4) ⊑ G}

/-- Adding one vertex can raise the four-cycle minimum-degree threshold by at most one. -/
abbrev statement : Prop :=
  ∀ n : ℕ, c4Threshold (n + 1) ≤ c4Threshold n + 1

theorem target : statement := sorry

end Statements.Erdos85ThresholdUpperStep

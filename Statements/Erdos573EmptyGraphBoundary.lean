import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

namespace Statements.Erdos573EmptyGraphBoundary

open SimpleGraph

/-- The empty one-vertex graph is admissible in the extremal class and has no
edges. This exercises both forbidden-copy predicates and the edge count. -/
abbrev statement : Prop :=
  ∃ G : SimpleGraph (Fin 1),
    (completeGraph (Fin 3)).Free G ∧ (cycleGraph 4).Free G ∧
      G.edgeSet.ncard = 0

theorem target : statement := sorry

end Statements.Erdos573EmptyGraphBoundary

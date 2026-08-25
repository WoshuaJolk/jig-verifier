import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A near-extremal C4-free core

Killing one edge from every copy of `C₄` produces a `C₄`-free subgraph.
Above the extremal threshold, the core's deficit from `ex(n, C₄)` is strictly
smaller than the original number of copies.
-/

open SimpleGraph

namespace Statements.Erdos60NearExtremalCore

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    extremalNumber n (cycleGraph 4) < G.edgeSet.ncard →
    ∃ H : SimpleGraph (Fin n),
      ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧
      (cycleGraph 4).Free H ∧
      G.edgeSet.ncard -
          {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard ≤
        H.edgeSet.ncard ∧
      H.edgeSet.ncard ≤ extremalNumber n (cycleGraph 4) ∧
      extremalNumber n (cycleGraph 4) - H.edgeSet.ncard <
        {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard ∧
      (∑ v, (G.degree v - H.degree v)) ≤
        2 * {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard

theorem target : statement := sorry

end Statements.Erdos60NearExtremalCore

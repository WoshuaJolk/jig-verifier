import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Edge-surplus lower bound for four-cycle copies

Deleting one edge from every copy of `C₄` leaves a `C₄`-free graph.  Therefore
the number of copies is at least the edge surplus above `ex(n, C₄)`.
-/

open SimpleGraph

namespace Statements.Erdos60EdgeSurplusCopies

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeFinset.card - extremalNumber n (cycleGraph 4) ≤
      {H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard

theorem target : statement := sorry

end Statements.Erdos60EdgeSurplusCopies

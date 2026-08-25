import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The defining one-copy consequence of `ex(n, C₄)`

Every graph with more than `ex(n, C₄)` edges contains a copy of `C₄`.  This is
the exact nonvacuity boundary beneath Erdős problem 60; the open problem asks
to strengthen one copy to order `sqrt n` copies.
-/

open SimpleGraph

namespace Statements.Erdos60AtLeastOneC4

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
    0 < ({H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard : ℕ)

theorem target : statement := sorry

end Statements.Erdos60AtLeastOneC4

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Deficit bound for extensions of a near-extremal C4-free core

A C4-free core with edge deficit `d` admits at most `d` additional edges in
any C4-free supergraph.
-/

open SimpleGraph

namespace Statements.Erdos60CoreDeficitSaturation

abbrev statement : Prop :=
  ∀ (n d : ℕ) (F H : SimpleGraph (Fin n))
    [DecidableRel F.Adj] [DecidableRel H.Adj],
    (cycleGraph 4).Free F →
    (cycleGraph 4).Free H →
    F ≤ H →
    F.edgeFinset.card + d = extremalNumber n (cycleGraph 4) →
    H.edgeFinset.card - F.edgeFinset.card ≤ d

theorem target : statement := sorry

end Statements.Erdos60CoreDeficitSaturation

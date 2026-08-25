import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Extremal C4-free graphs are saturated

Adding any missing edge to a C4-free graph with `ex(n,C4)` edges destroys
`C₄`-freeness.
-/

open SimpleGraph

namespace Statements.Erdos60ExtremalSaturation

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (cycleGraph 4).Free G →
    G.edgeFinset.card = extremalNumber n (cycleGraph 4) →
    ∀ u v : Fin n, u ≠ v → ¬G.Adj u v →
      ¬(cycleGraph 4).Free (G ⊔ edge u v)

theorem target : statement := sorry

end Statements.Erdos60ExtremalSaturation

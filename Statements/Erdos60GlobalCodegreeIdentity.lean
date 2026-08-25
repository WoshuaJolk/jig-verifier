import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Global codegree identity for labelled four-cycles

Partition labelled copies of `C₄` by the ordered images of the opposite
vertices `0` and `2`.  For each ordered distinct vertex pair `(u,v)`, the
fiber has exactly `codeg(u,v) * (codeg(u,v) - 1)` elements.
-/

open SimpleGraph

namespace Statements.Erdos60GlobalCodegreeIdentity

abbrev DistinctVertexPairs (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≠ p.2}

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    Nat.card ((cycleGraph 4).Copy G) =
      ∑ p : DistinctVertexPairs n,
        (G.commonNeighbors p.1.1 p.1.2).ncard *
          ((G.commonNeighbors p.1.1 p.1.2).ncard - 1)

theorem target : statement := sorry

end Statements.Erdos60GlobalCodegreeIdentity

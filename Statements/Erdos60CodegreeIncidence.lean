import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
# Exact degree-codegree incidence identity

Ordered length-two paths can be counted either by their middle vertex or by
their ordered pair of endpoints.
-/

open SimpleGraph
open scoped BigOperators

namespace Statements.Erdos60CodegreeIncidence

abbrev DistinctPairs (n : ℕ) :=
  {p : Fin n × Fin n // p.1 ≠ p.2}

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∑ p : DistinctPairs n,
      (G.commonNeighbors p.1.1 p.1.2).ncard) =
    ∑ x : Fin n, G.degree x * (G.degree x - 1)

theorem target : statement := sorry

end Statements.Erdos60CodegreeIncidence

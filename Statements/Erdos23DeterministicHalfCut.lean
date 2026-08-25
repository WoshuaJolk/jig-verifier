import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23DeterministicHalfCut

open scoped Classical in
/-- Every finite simple graph has a bipartite subgraph retaining at least
half of its edges (equivalently, at least `ceil(m / 2)`). -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ (H : SimpleGraph V),
      H ≤ G ∧ H.IsBipartite ∧
        G.edgeFinset.card ≤ 2 * H.edgeFinset.card

theorem target : statement := sorry

end Statements.Erdos23DeterministicHalfCut

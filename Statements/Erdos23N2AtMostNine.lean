import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23N2AtMostNine

open scoped Classical in
/-- The full `n = 2` range through nine edges, including isolated vertices. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      G.edgeFinset.card ≤ 9 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧
            (G.edgeFinset \ H.edgeFinset).card ≤ 4

theorem target : statement := sorry

end Statements.Erdos23N2AtMostNine

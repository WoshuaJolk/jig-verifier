import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23NeighborhoodCut

open scoped Classical in
/-- The conjectured deletion bound follows whenever one vertex has enough
degree mass in its neighborhood. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      (∃ v : V,
        G.edgeFinset.card ≤
          n ^ 2 + ∑ w ∈ G.neighborFinset v, G.degree w) →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧
            (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2

theorem target : statement := sorry

end Statements.Erdos23NeighborhoodCut

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23IndependentCut

open scoped Classical in
/-- A sufficiently large degree-weighted independent set gives the required cut. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      (∃ S : Finset V,
        G.IsIndepSet (S : Set V) ∧
          G.edgeFinset.card ≤ n ^ 2 + ∑ v ∈ S, G.degree v) →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧
            (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2

theorem target : statement := sorry

end Statements.Erdos23IndependentCut

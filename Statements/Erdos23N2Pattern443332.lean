import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23N2Pattern443332

open scoped Classical in
/-- The terminal `m = 15` degree pattern `4² 3⁶ 2²` satisfies the `n = 2`
bipartization bound. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      G.edgeFinset.card = 15 →
      (∀ x : V, G.degree x = 2 ∨ G.degree x = 3 ∨ G.degree x = 4) →
      ((Finset.univ : Finset V).filter fun x => G.degree x = 4).card = 2 →
      ((Finset.univ : Finset V).filter fun x => G.degree x = 3).card = 6 →
      ((Finset.univ : Finset V).filter fun x => G.degree x = 2).card = 2 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧
            (G.edgeFinset \ H.edgeFinset).card ≤ 4

theorem target : statement := sorry

end Statements.Erdos23N2Pattern443332

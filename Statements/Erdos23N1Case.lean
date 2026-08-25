import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23N1Case

open scoped Classical in
/-- The conjectured bipartization bound holds when `n = 1`. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 5 →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      ∃ (H : SimpleGraph V),
        H ≤ G ∧ H.IsBipartite ∧
          (G.edgeFinset \ H.edgeFinset).card ≤ 1

theorem target : statement := sorry

end Statements.Erdos23N1Case

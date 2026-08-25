import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23TriangleFreeBipartize

open scoped Classical in
/-- Erdős Problem 23: every triangle-free graph on `5 * n` vertices can be
made bipartite by deleting at most `n ^ 2` edges. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      ∃ (H : SimpleGraph V),
        H ≤ G ∧ H.IsBipartite ∧
          (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2

theorem target : statement := sorry

end Statements.Erdos23TriangleFreeBipartize

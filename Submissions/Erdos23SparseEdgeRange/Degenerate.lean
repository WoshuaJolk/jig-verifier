import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Submissions.Erdos23SparseEdgeRange.Degenerate

open scoped Classical in
theorem proof :
    False →
      ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
        ∀ (G : SimpleGraph V), G.CliqueFree 3 →
          G.edgeFinset.card ≤ n ^ 2 →
            ∃ (H : SimpleGraph V),
              H ≤ G ∧ H.IsBipartite ∧
                (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2 :=
  False.elim

end Submissions.Erdos23SparseEdgeRange.Degenerate

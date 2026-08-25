import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Submissions.Erdos23SparseEdgeRange.Direct

open scoped Classical in
theorem proof :
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        G.edgeFinset.card ≤ n ^ 2 →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2 := by
  intro n V _ _ G _ hedge
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · exact (SimpleGraph.colorable_one_iff.mpr rfl).mono (by decide)
  · exact (Finset.card_le_card Finset.sdiff_subset).trans hedge

end Submissions.Erdos23SparseEdgeRange.Direct

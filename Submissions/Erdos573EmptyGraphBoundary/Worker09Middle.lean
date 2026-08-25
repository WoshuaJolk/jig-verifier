import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

namespace Submissions.Erdos573EmptyGraphBoundary.Worker09Middle

open SimpleGraph

theorem empty_free {α β : Type*} (A : SimpleGraph α)
    (h : ∃ u v, A.Adj u v) :
    A.Free (⊥ : SimpleGraph β) := by
  rintro ⟨copy⟩
  rcases h with ⟨u, v, huv⟩
  simpa using copy.toHom.map_adj huv

theorem proof :
    ∃ G : SimpleGraph (Fin 1),
      (completeGraph (Fin 3)).Free G ∧ (cycleGraph 4).Free G ∧
        G.edgeSet.ncard = 0 := by
  refine ⟨⊥, empty_free _ ?_, empty_free _ ?_, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨0, 1, by decide⟩

end Submissions.Erdos573EmptyGraphBoundary.Worker09Middle

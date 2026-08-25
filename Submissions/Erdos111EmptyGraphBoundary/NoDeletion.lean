import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Submissions.Erdos111EmptyGraphBoundary.NoDeletion

def CanBipartizeByDeletingAtMost {V : Type} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Finset (Sym2 V), E.card ≤ m ∧
    (G.deleteEdges (E : Set (Sym2 V))).IsBipartite

theorem proof :
    ∀ (V : Type) [Fintype V],
      CanBipartizeByDeletingAtMost (⊥ : SimpleGraph V) 0 := by
  intro V _
  refine ⟨∅, by simp, ?_⟩
  have hE : ((↑(∅ : Finset (Sym2 V)) : Set (Sym2 V))) = ∅ := by
    ext e
    simp
  rw [hE]
  rw [SimpleGraph.deleteEdges_empty]
  change Nonempty ((⊥ : SimpleGraph V).Coloring (Fin 2))
  exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (by simp)⟩

end Submissions.Erdos111EmptyGraphBoundary.NoDeletion

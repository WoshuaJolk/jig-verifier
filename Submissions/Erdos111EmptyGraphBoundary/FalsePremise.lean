import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Submissions.Erdos111EmptyGraphBoundary.FalsePremise

def CanBipartizeByDeletingAtMost {V : Type} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Finset (Sym2 V), E.card ≤ m ∧
    (G.deleteEdges (E : Set (Sym2 V))).IsBipartite

theorem proof :
    False →
      ∀ (V : Type) [Fintype V],
        CanBipartizeByDeletingAtMost (⊥ : SimpleGraph V) 0 := by
  intro h
  exact h.elim

end Submissions.Erdos111EmptyGraphBoundary.FalsePremise

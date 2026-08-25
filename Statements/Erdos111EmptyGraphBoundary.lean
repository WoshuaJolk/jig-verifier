import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Statements.Erdos111EmptyGraphBoundary

def CanBipartizeByDeletingAtMost {V : Type} [Fintype V]
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ E : Finset (Sym2 V), E.card ≤ m ∧
    (G.deleteEdges (E : Set (Sym2 V))).IsBipartite

abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V],
    CanBipartizeByDeletingAtMost (⊥ : SimpleGraph V) 0

theorem target : statement := sorry

end Statements.Erdos111EmptyGraphBoundary

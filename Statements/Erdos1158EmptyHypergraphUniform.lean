import Mathlib.Data.Finset.Card

namespace Statements.Erdos1158EmptyHypergraphUniform

def Uniform {n : ℕ} (E : Finset (Finset (Fin n))) (t : ℕ) : Prop :=
  ∀ e ∈ E, e.card = t

/-- The empty hypergraph is uniform in every degree. -/
abbrev statement : Prop :=
  ∀ n t : ℕ, Uniform (n := n) ∅ t

theorem target : statement := sorry

end Statements.Erdos1158EmptyHypergraphUniform

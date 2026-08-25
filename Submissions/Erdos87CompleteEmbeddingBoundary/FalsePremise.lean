import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Submissions.Erdos87CompleteEmbeddingBoundary.FalsePremise

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

theorem proof :
    False →
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ContainsCopy G (⊤ : SimpleGraph (Fin n)) := by
  intro h
  exact h.elim

end Submissions.Erdos87CompleteEmbeddingBoundary.FalsePremise

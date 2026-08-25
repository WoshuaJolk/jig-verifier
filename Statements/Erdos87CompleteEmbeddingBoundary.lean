import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Statements.Erdos87CompleteEmbeddingBoundary

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ContainsCopy G (⊤ : SimpleGraph (Fin n))

theorem target : statement := sorry

end Statements.Erdos87CompleteEmbeddingBoundary

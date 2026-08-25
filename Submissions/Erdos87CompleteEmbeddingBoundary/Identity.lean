import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Submissions.Erdos87CompleteEmbeddingBoundary.Identity

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ContainsCopy G (⊤ : SimpleGraph (Fin n)) := by
  intro n G
  refine ⟨id, Function.injective_id, ?_⟩
  intro u v huv
  simp only [SimpleGraph.top_adj]
  exact huv.ne

end Submissions.Erdos87CompleteEmbeddingBoundary.Identity

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Submissions.Erdos159C4EmbeddingBoundary.Identity

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

theorem proof :
    ContainsCopy (SimpleGraph.cycleGraph 4) (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨id, Function.injective_id, ?_⟩
  intro u v huv
  simp only [SimpleGraph.top_adj]
  exact huv.ne

end Submissions.Erdos159C4EmbeddingBoundary.Identity

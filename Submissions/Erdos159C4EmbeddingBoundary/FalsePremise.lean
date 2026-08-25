import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Submissions.Erdos159C4EmbeddingBoundary.FalsePremise

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

theorem proof :
    False →
      ContainsCopy (SimpleGraph.cycleGraph 4) (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  exact h.elim

end Submissions.Erdos159C4EmbeddingBoundary.FalsePremise

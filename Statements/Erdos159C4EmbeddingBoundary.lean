import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace Statements.Erdos159C4EmbeddingBoundary

def ContainsCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧
    ∀ ⦃u v⦄, G.Adj u v → H.Adj (f u) (f v)

abbrev statement : Prop :=
  ContainsCopy (SimpleGraph.cycleGraph 4) (⊤ : SimpleGraph (Fin 4))

theorem target : statement := sorry

end Statements.Erdos159C4EmbeddingBoundary

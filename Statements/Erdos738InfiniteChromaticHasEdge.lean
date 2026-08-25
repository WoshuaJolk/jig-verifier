import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Statements.Erdos738InfiniteChromaticHasEdge

universe u

def InfiniteChromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ∀ color : V → Fin k,
    ∃ u v : V, G.Adj u v ∧ color u = color v

/-- An infinite-chromatic graph is nonempty at the first tree-embedding
level: it contains an edge. -/
abbrev statement : Prop :=
  ∀ (V : Type u) [Infinite V], ∀ G : SimpleGraph V,
    InfiniteChromatic G → ∃ u v : V, G.Adj u v

theorem target : statement := sorry

end Statements.Erdos738InfiniteChromaticHasEdge

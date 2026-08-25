import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Submissions.Erdos738InfiniteChromaticHasEdge.Direct

universe u

def InfiniteChromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ∀ color : V → Fin k,
    ∃ u v : V, G.Adj u v ∧ color u = color v

theorem proof :
    ∀ (V : Type u) [Infinite V], ∀ G : SimpleGraph V,
      InfiniteChromatic G → ∃ u v : V, G.Adj u v := by
  intro V _ G hG
  obtain ⟨u, v, huv, _⟩ := hG 1 (fun _ => 0)
  exact ⟨u, v, huv⟩

end Submissions.Erdos738InfiniteChromaticHasEdge.Direct

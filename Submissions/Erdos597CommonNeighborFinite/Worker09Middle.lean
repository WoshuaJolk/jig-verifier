import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Submissions.Erdos597CommonNeighborFinite.Worker09Middle

def HasCountableBiclique {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ L R : Set V,
    Disjoint L R ∧ #L = ℵ₀ ∧ #R = ℵ₀ ∧
      ∀ l ∈ L, ∀ r ∈ R, G.Adj l r

def CommonNeighbors {V : Type} (G : SimpleGraph V) (L : Set V) : Set V :=
  {v | ∀ l ∈ L, G.Adj l v}

theorem proof :
    ∀ (V : Type) (G : SimpleGraph V),
      ¬HasCountableBiclique G →
      ∀ L : Set V, #L = ℵ₀ →
        #(CommonNeighbors G L) < ℵ₀ := by
  intro V G hG L hL
  by_contra hfinite
  have hinfinite : ℵ₀ ≤ #(CommonNeighbors G L) := not_lt.mp hfinite
  rcases Cardinal.le_mk_iff_exists_subset.mp hinfinite with ⟨R, hRsub, hR⟩
  apply hG
  refine ⟨L, R, ?_, hL, hR, ?_⟩
  · rw [Set.disjoint_left]
    intro v hvL hvR
    exact G.loopless.irrefl v (hRsub hvR v hvL)
  · intro l hl r hr
    exact hRsub hr l hl

end Submissions.Erdos597CommonNeighborFinite.Worker09Middle

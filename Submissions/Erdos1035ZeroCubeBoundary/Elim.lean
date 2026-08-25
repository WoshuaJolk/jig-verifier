import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Submissions.Erdos1035ZeroCubeBoundary.Elim

def CubeAdjacent {n : ℕ} (u v : Fin n → Bool) : Prop :=
  ∃ i : Fin n, u i ≠ v i ∧
    ∀ j : Fin n, j ≠ i → u j = v j

def ContainsHypercube (n : ℕ) (G : SimpleGraph (Fin (2 ^ n))) : Prop :=
  ∃ φ : (Fin n → Bool) → Fin (2 ^ n), Function.Injective φ ∧
    ∀ u v, CubeAdjacent u v → G.Adj (φ u) (φ v)

theorem proof :
    ∀ G : SimpleGraph (Fin (2 ^ 0)), ContainsHypercube 0 G := by
  intro G
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro u v huv
    exact Subsingleton.elim u v
  · intro u v huv
    obtain ⟨i, hi, hrest⟩ := huv
    exact Fin.elim0 i

end Submissions.Erdos1035ZeroCubeBoundary.Elim

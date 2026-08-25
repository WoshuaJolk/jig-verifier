import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace Submissions.Erdos151UniversalTransversal.Direct

open SimpleGraph

def CliqueTransversal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ K : Finset V, 2 ≤ K.card →
    Maximal G.IsClique (K : Set V) →
      ∃ v ∈ K, v ∈ T

theorem proof :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      CliqueTransversal G Finset.univ := by
  intro n G K hcard hmax
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
  exact ⟨v, hv, Finset.mem_univ v⟩

end Submissions.Erdos151UniversalTransversal.Direct

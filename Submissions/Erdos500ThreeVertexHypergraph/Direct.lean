import Mathlib

namespace Submissions.Erdos500ThreeVertexHypergraph.Direct

abbrev ThreeGraph (n : ℕ) := Finset (Finset (Fin n))

def IsThreeUniform {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ e ∈ E, e.card = 3

def IsK4Free {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card = 3 ∧ T ∉ E

theorem proof :
    IsThreeUniform ({Finset.univ} : ThreeGraph 3) ∧
      IsK4Free ({Finset.univ} : ThreeGraph 3) := by
  constructor
  · intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    simp
  · intro S hS
    have hle : S.card ≤ Fintype.card (Fin 3) := Finset.card_le_univ S
    simp at hle
    omega

end Submissions.Erdos500ThreeVertexHypergraph.Direct

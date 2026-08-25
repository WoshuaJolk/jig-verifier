import Mathlib

namespace Submissions.Erdos500ThreeVertexHypergraph.Degenerate

abbrev ThreeGraph (n : ℕ) := Finset (Finset (Fin n))

def IsThreeUniform {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ e ∈ E, e.card = 3

def IsK4Free {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card = 3 ∧ T ∉ E

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof :
    False →
      (IsThreeUniform ({Finset.univ} : ThreeGraph 3) ∧
        IsK4Free ({Finset.univ} : ThreeGraph 3)) :=
  False.elim

end Submissions.Erdos500ThreeVertexHypergraph.Degenerate

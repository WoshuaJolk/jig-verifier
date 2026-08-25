import Mathlib

namespace Statements.Erdos500ThreeVertexHypergraph

abbrev ThreeGraph (n : ℕ) := Finset (Finset (Fin n))

def IsThreeUniform {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ e ∈ E, e.card = 3

def IsK4Free {n : ℕ} (E : ThreeGraph n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 →
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card = 3 ∧ T ∉ E

/-- The unique 3-edge on three vertices is uniform and vacuously K4-free. -/
abbrev statement : Prop :=
  IsThreeUniform ({Finset.univ} : ThreeGraph 3) ∧
    IsK4Free ({Finset.univ} : ThreeGraph 3)

theorem target : statement := sorry

end Statements.Erdos500ThreeVertexHypergraph

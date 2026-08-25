import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Submissions.Erdos165RamseyBoundary.Worker09Small

def RamseyProperty (N k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ triangle : Finset (Fin N), G.IsNClique 3 triangle) ∨
    (∃ independent : Finset (Fin N), Gᶜ.IsNClique k independent)

theorem proof : ¬RamseyProperty 0 1 ∧ RamseyProperty 1 1 := by
  constructor
  · intro h
    simpa [RamseyProperty] using h (⊥ : SimpleGraph (Fin 0))
  · simp [RamseyProperty]

end Submissions.Erdos165RamseyBoundary.Worker09Small

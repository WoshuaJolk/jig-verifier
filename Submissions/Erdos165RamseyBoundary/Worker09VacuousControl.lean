import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Submissions.Erdos165RamseyBoundary.Worker09VacuousControl

def RamseyProperty (N k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ triangle : Finset (Fin N), G.IsNClique 3 triangle) ∨
    (∃ independent : Finset (Fin N), Gᶜ.IsNClique k independent)

theorem proof (h : False) : ¬RamseyProperty 0 1 ∧ RamseyProperty 1 1 := h.elim

end Submissions.Erdos165RamseyBoundary.Worker09VacuousControl

import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Statements.Erdos165RamseyBoundary

def RamseyProperty (N k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ triangle : Finset (Fin N), G.IsNClique 3 triangle) ∨
    (∃ independent : Finset (Fin N), Gᶜ.IsNClique k independent)

abbrev statement : Prop :=
  ¬RamseyProperty 0 1 ∧ RamseyProperty 1 1

theorem target : statement := sorry

end Statements.Erdos165RamseyBoundary

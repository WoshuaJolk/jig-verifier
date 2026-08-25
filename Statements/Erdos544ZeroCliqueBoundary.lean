import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos544ZeroCliqueBoundary

def IsGraphRamsey (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ (Gᶜ).CliqueFree l)

/-- A zero-clique is present in every graph. -/
abbrev statement : Prop :=
  ∀ n l : ℕ, IsGraphRamsey n 0 l

theorem target : statement := sorry

end Statements.Erdos544ZeroCliqueBoundary

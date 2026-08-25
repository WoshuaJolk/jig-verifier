import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic

namespace Statements.Erdos1013MinimumOrderNonnegative

noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ |
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = k}

/-- The minimum triangle-free chromatic order, cast to the reals, is nonnegative. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 0 ≤ (h3 k : ℝ)

theorem target : statement := sorry

end Statements.Erdos1013MinimumOrderNonnegative

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos1013MinimumOrderNonnegative.Direct

noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ |
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = k}

 theorem proof : ∀ k : ℕ, 0 ≤ (h3 k : ℝ) := by
  intro k
  exact_mod_cast Nat.zero_le (h3 k)

end Submissions.Erdos1013MinimumOrderNonnegative.Direct

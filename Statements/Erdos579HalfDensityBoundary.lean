import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Instances.Nat

open Filter SimpleGraph
open scoped Classical

namespace Statements.Erdos579HalfDensityBoundary

abbrev octahedron : SimpleGraph (Σ _ : Fin 3, Fin 2) :=
  completeMultipartiteGraph (fun _ : Fin 3 ↦ Fin 2)

/-- The impossible half-density boundary of Erdős Problem 579. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n), octahedron.Free G →
      (1 / 2 : ℝ) * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
        c * n ≤ (G.indepNum : ℝ)

theorem target : statement := sorry

end Statements.Erdos579HalfDensityBoundary

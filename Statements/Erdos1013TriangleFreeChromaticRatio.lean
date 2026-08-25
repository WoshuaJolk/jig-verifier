import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos1013TriangleFreeChromaticRatio

/-- The least order of a finite triangle-free graph of chromatic number `k`. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ |
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ G.chromaticNumber = k}

/-- Erdős Problem 1013: consecutive values of `h3` have asymptotic ratio one. -/
abbrev statement : Prop :=
  Filter.Tendsto
    (fun k : ℕ => (h3 (k + 1) : ℝ) / (h3 k : ℝ))
    Filter.atTop
    (nhds 1)

theorem target : statement := sorry

end Statements.Erdos1013TriangleFreeChromaticRatio

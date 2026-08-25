import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos573TriangleFourCycleExtremal

open Filter SimpleGraph Topology

noncomputable def extremal (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    (completeGraph (Fin 3)).Free G ∧ (cycleGraph 4).Free G ∧
      G.edgeSet.ncard = m}

/-- Erdős Problem 573: the maximum number of edges in an `n`-vertex graph
containing neither a triangle nor a four-cycle is asymptotic to
`(n / 2) ^ (3 / 2)`. -/
abbrev statement : Prop :=
  Tendsto
    (fun n : ℕ ↦
      (extremal n : ℝ) / (((n : ℝ) / 2) ^ (3 / 2 : ℝ)))
    atTop (𝓝 1)

theorem target : statement := sorry

end Statements.Erdos573TriangleFourCycleExtremal

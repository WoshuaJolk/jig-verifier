import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Instances.Real.Lemmas

namespace Statements.Erdos917SixCriticalEdgeDensity

open Filter

def IsEdgeCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < k

noncomputable def maximumCriticalEdges (k n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : SimpleGraph (Fin n) =>
      if IsEdgeCritical G k then G.edgeFinset.card else 0

/-- Erdős Problem 917, the concrete six-chromatic asymptotic conjecture. -/
abbrev statement : Prop :=
  Tendsto
    (fun n : ℕ => (maximumCriticalEdges 6 n : ℝ) / (n : ℝ) ^ 2)
    atTop
    (nhds (1 / 4 : ℝ))

theorem target : statement := sorry

end Statements.Erdos917SixCriticalEdgeDensity

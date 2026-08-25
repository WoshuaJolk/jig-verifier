import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic

namespace Statements.Erdos917MaximumNonnegative

def IsEdgeCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < k

noncomputable def maximumCriticalEdges (k n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : SimpleGraph (Fin n) =>
      if IsEdgeCritical G k then G.edgeFinset.card else 0

abbrev statement : Prop :=
  ∀ k n : ℕ, 0 ≤ (maximumCriticalEdges k n : ℝ)

theorem target : statement := sorry

end Statements.Erdos917MaximumNonnegative

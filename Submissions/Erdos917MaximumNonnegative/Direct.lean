import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic

namespace Submissions.Erdos917MaximumNonnegative.Direct

def IsEdgeCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < k

noncomputable def maximumCriticalEdges (k n : ℕ) : ℕ :=
  open scoped Classical in
    Finset.univ.sup fun G : SimpleGraph (Fin n) =>
      if IsEdgeCritical G k then G.edgeFinset.card else 0

theorem proof :
    ∀ k n : ℕ, 0 ≤ (maximumCriticalEdges k n : ℝ) := by
  intro k n
  exact_mod_cast Nat.zero_le (maximumCriticalEdges k n)

end Submissions.Erdos917MaximumNonnegative.Direct

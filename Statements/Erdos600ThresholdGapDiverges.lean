import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Topology.Instances.Nat

/-!
# Erdős problem 600(i)

Let `e(n,r)` be the least edge threshold forcing one edge to lie in at least
`r` triangles, among graphs in which every edge lies in a triangle. Do
successive thresholds diverge apart?
-/

open Filter

namespace Statements.Erdos600ThresholdGapDiverges

open scoped Classical

noncomputable def trianglesContaining {α : Type*} [Fintype α]
    (G : SimpleGraph α) (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t => uv.toFinset ⊆ t)

def ThresholdProperty (n e r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
    (∀ uv ∈ G.edgeFinset, (trianglesContaining G uv).Nonempty) →
      ∃ uv ∈ G.edgeFinset, r ≤ (trianglesContaining G uv).card

noncomputable def threshold (n r : ℕ) : ℕ :=
  sInf {e | ThresholdProperty n e r}

abbrev statement : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Tendsto
      (fun n : ℕ => (threshold n (r + 1) : ℝ) - (threshold n r : ℝ))
      atTop atTop

theorem target : statement := sorry

end Statements.Erdos600ThresholdGapDiverges

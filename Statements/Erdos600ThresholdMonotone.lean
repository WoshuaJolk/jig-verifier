import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Monotonicity of the Erdős 600 edge threshold

Requiring an edge to lie in one more triangle cannot lower the least edge
threshold.
-/

namespace Statements.Erdos600ThresholdMonotone

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
  ∀ n r : ℕ, threshold n r ≤ threshold n (r + 1)

theorem target : statement := sorry

end Statements.Erdos600ThresholdMonotone

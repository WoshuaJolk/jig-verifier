import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

namespace Submissions.Erdos600ThresholdMonotone.Order

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

private theorem threshold_set_nonempty (n r : ℕ) :
    {e | ThresholdProperty n e r}.Nonempty := by
  refine ⟨n.choose 2 + 1, ?_⟩
  intro G hEdges
  have hmax : G.edgeFinset.card ≤ n.choose 2 := by
    simpa using G.card_edgeFinset_le_card_choose_two
  omega

theorem proof : ∀ n r : ℕ, threshold n r ≤ threshold n (r + 1) := by
  intro n r
  apply Nat.sInf_le
  have hstrong :
      ThresholdProperty n (threshold n (r + 1)) (r + 1) := by
    exact Nat.sInf_mem (threshold_set_nonempty n (r + 1))
  intro G hEdges hTriangles
  obtain ⟨uv, huv, hcount⟩ := hstrong G hEdges hTriangles
  exact ⟨uv, huv, le_trans (Nat.le_succ r) hcount⟩

end Submissions.Erdos600ThresholdMonotone.Order

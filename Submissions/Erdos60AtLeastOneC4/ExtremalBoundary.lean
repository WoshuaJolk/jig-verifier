import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open SimpleGraph

namespace Submissions.Erdos60AtLeastOneC4.ExtremalBoundary

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
      0 < ({H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard : ℕ) := by
  intro n G _ h
  have hcont : cycleGraph 4 ⊑ G := by
    apply IsContained.of_extremalNumber_lt_card_edgeFinset
    simpa using h
  obtain ⟨H', ⟨e⟩⟩ := hcont.exists_iso_subgraph
  rw [Set.ncard_pos]
  exact ⟨H', ⟨e.symm⟩⟩

end Submissions.Erdos60AtLeastOneC4.ExtremalBoundary

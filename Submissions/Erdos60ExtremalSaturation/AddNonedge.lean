import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos60ExtremalSaturation.AddNonedge

theorem proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (cycleGraph 4).Free G →
      G.edgeFinset.card = extremalNumber n (cycleGraph 4) →
      ∀ u v : Fin n, u ≠ v → ¬G.Adj u v →
        ¬(cycleGraph 4).Free (G ⊔ edge u v) := by
  intro n G _ _ hcard u v huv hnuv hnewfree
  have hcardNew :
      extremalNumber n (cycleGraph 4) <
        (G ⊔ edge u v).edgeFinset.card := by
    rw [G.card_edgeFinset_sup_edge hnuv huv, hcard]
    omega
  have hcont : cycleGraph 4 ⊑ (G ⊔ edge u v) := by
    apply IsContained.of_extremalNumber_lt_card_edgeFinset
    simpa using hcardNew
  exact hnewfree hcont

end Submissions.Erdos60ExtremalSaturation.AddNonedge

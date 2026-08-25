import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

open SimpleGraph

namespace Submissions.Erdos60CoreDeficitSaturation.DeficitBound

theorem proof :
    ∀ (n d : ℕ) (F H : SimpleGraph (Fin n))
      [DecidableRel F.Adj] [DecidableRel H.Adj],
      (cycleGraph 4).Free F →
      (cycleGraph 4).Free H →
      F ≤ H →
      F.edgeFinset.card + d = extremalNumber n (cycleGraph 4) →
      H.edgeFinset.card - F.edgeFinset.card ≤ d := by
  intro n d F H _ _ _ hH _ hdef
  have hle :
      H.edgeFinset.card ≤ extremalNumber n (cycleGraph 4) := by
    simpa using card_edgeFinset_le_extremalNumber hH
  omega

end Submissions.Erdos60CoreDeficitSaturation.DeficitBound

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open SimpleGraph Filter

namespace Submissions.Erdos60LowSurplusCore.Composer

noncomputable abbrev Copies {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  {H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard

abbrev EdgeSurplusBound : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeFinset.card - extremalNumber n (cycleGraph 4) ≤ Copies G

abbrev Root : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
        c * Real.sqrt (n : ℝ) ≤ (Copies G : ℝ)

abbrev LowSurplusCore : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
        (↑(G.edgeFinset.card - extremalNumber n (cycleGraph 4)) : ℝ) <
            c * Real.sqrt (n : ℝ) →
        c * Real.sqrt (n : ℝ) ≤ (Copies G : ℝ)

theorem proof :
    EdgeSurplusBound → (Root ↔ LowSurplusCore) := by
  intro hsurplus
  constructor
  · rintro ⟨c, hc, hroot⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [hroot] with n hn
    intro G _ hedge _
    exact hn G hedge
  · rintro ⟨c, hc, hcore⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [hcore] with n hn
    intro G _ hedge
    by_cases hlow :
        (↑(G.edgeFinset.card - extremalNumber n (cycleGraph 4)) : ℝ) <
          c * Real.sqrt (n : ℝ)
    · exact hn G hedge hlow
    · have hthreshold :
          c * Real.sqrt (n : ℝ) ≤
            (↑(G.edgeFinset.card -
              extremalNumber n (cycleGraph 4)) : ℝ) := le_of_not_gt hlow
      have hcount :
          (↑(G.edgeFinset.card -
              extremalNumber n (cycleGraph 4)) : ℝ) ≤
            (Copies G : ℝ) := by
        exact_mod_cast hsurplus n G
      exact hthreshold.trans hcount

end Submissions.Erdos60LowSurplusCore.Composer

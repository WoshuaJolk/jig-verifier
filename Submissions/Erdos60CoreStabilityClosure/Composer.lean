import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open SimpleGraph Filter
open scoped BigOperators

namespace Submissions.Erdos60CoreStabilityClosure.Composer

noncomputable abbrev Copies {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  {C : G.Subgraph | Nonempty (C.coe ≃g cycleGraph 4)}.ncard

abbrev NearCoreReduction : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    extremalNumber n (cycleGraph 4) < G.edgeSet.ncard →
    ∃ H : SimpleGraph (Fin n),
      ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧
      (cycleGraph 4).Free H ∧
      G.edgeSet.ncard - Copies G ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard ≤ extremalNumber n (cycleGraph 4) ∧
      extremalNumber n (cycleGraph 4) - H.edgeSet.ncard < Copies G ∧
      (∑ v, (G.degree v - H.degree v)) ≤ 2 * Copies G

abbrev CoreStability : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G H : SimpleGraph (Fin n))
        [DecidableRel G.Adj] [DecidableRel H.Adj],
        H ≤ G →
        (cycleGraph 4).Free H →
        G.edgeSet.ncard - Copies G ≤ H.edgeSet.ncard →
        H.edgeSet.ncard ≤ extremalNumber n (cycleGraph 4) →
        extremalNumber n (cycleGraph 4) - H.edgeSet.ncard < Copies G →
        (∑ v, (G.degree v - H.degree v)) ≤ 2 * Copies G →
        extremalNumber n (cycleGraph 4) < G.edgeSet.ncard →
        (↑(G.edgeSet.ncard - extremalNumber n (cycleGraph 4)) : ℝ) <
            c * Real.sqrt (n : ℝ) →
        c * Real.sqrt (n : ℝ) ≤ (Copies G : ℝ)

abbrev LowSurplusCore : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
        (↑(G.edgeFinset.card - extremalNumber n (cycleGraph 4)) : ℝ) <
            c * Real.sqrt (n : ℝ) →
        c * Real.sqrt (n : ℝ) ≤ (Copies G : ℝ)

private theorem edgeSet_ncard_eq {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

theorem proof :
    NearCoreReduction → CoreStability → LowSurplusCore := by
  rintro hreduce ⟨c, hc, hstability⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hstability] with n hn
  intro G _ hedge hlow
  have hedgeSet :
      extremalNumber n (cycleGraph 4) < G.edgeSet.ncard := by
    simpa [edgeSet_ncard_eq G] using hedge
  have hlowSet :
      (↑(G.edgeSet.ncard - extremalNumber n (cycleGraph 4)) : ℝ) <
        c * Real.sqrt (n : ℝ) := by
    simpa [edgeSet_ncard_eq G] using hlow
  obtain ⟨H, hdec, hHG, hfree, hkill, hmax, hdeficit, hdegree⟩ :=
    hreduce n G hedgeSet
  letI : DecidableRel H.Adj := hdec
  exact hn G H hHG hfree hkill hmax hdeficit hdegree hedgeSet hlowSet

end Submissions.Erdos60CoreStabilityClosure.Composer

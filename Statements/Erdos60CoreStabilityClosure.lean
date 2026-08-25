import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Card

open SimpleGraph Filter
open scoped BigOperators

namespace Statements.Erdos60CoreStabilityClosure

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

/-- The near-extremal core reduction converts a sharp stability theorem for
the resulting graph/core pairs into the exact low-surplus residual. -/
abbrev statement : Prop :=
  NearCoreReduction → CoreStability → LowSurplusCore

theorem target : statement := sorry

end Statements.Erdos60CoreStabilityClosure

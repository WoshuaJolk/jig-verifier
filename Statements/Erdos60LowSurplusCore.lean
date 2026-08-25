import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Real.Sqrt

open SimpleGraph Filter

namespace Statements.Erdos60LowSurplusCore

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

/-- Given the proved edge-surplus bound, Erdős 60 is exactly its low-surplus
near-extremal regime: graphs with larger surplus already have enough copies. -/
abbrev statement : Prop :=
  EdgeSurplusBound → (Root ↔ LowSurplusCore)

theorem target : statement := sorry

end Statements.Erdos60LowSurplusCore

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Topology.Instances.Nat
import Mathlib.Analysis.Real.Sqrt

/-!
# Erdős problem 60: supersaturation of four-cycles

Erdős and Simonovits asked whether every graph with more than
`ex(n, C₄)` edges contains at least a constant times `sqrt n` copies of `C₄`
for all sufficiently large `n`.

The count is Mathlib's subgraph copy count: two embeddings with the same image
are one copy.  This is the exact proposition in
`google-deepmind/formal-conjectures`, Erdős problem 60.
-/

open SimpleGraph Filter

namespace Statements.Erdos60C4Supersaturation

abbrev statement : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        extremalNumber n (cycleGraph 4) < G.edgeFinset.card →
        c * Real.sqrt (n : ℝ) ≤
          ({H' : G.Subgraph | Nonempty (H'.coe ≃g cycleGraph 4)}.ncard : ℝ)

theorem target : statement := sorry

end Statements.Erdos60C4Supersaturation

import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Nat.Sqrt

/-!
# Minimum-path stability conjecture for near-extremal C4-free graphs

This is the remaining quantitative step after reducing added-edge four-cycles
to simple length-three paths.  The deficit term is necessary for applying the
estimate to a C4-free core below the extremal number.
-/

open SimpleGraph

namespace Statements.Erdos60MinimumPathStability

abbrev SimpleThreePaths {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) :=
  {p : Fin n × Fin n //
    G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v ∧
      p.1 ≠ v ∧ p.2 ≠ u}

abbrev statement : Prop :=
  ∃ K N : ℕ, 0 < K ∧
    ∀ (n : ℕ), N ≤ n →
    ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      (cycleGraph 4).Free F →
      ∀ (d : ℕ),
        F.edgeFinset.card + d = extremalNumber n (cycleGraph 4) →
        ∀ u v : Fin n, u ≠ v → ¬F.Adj u v →
          ¬(cycleGraph 4).Free (F ⊔ edge u v) →
          Nat.sqrt n ≤
            K * (Nat.card (SimpleThreePaths F u v) + d)

theorem target : statement := sorry

end Statements.Erdos60MinimumPathStability

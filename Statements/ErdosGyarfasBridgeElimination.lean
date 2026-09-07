import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Jig-ready canonical proposition for bridge elimination in a minimum-order
Erdős--Gyárfás counterexample.

The graph-theoretic proof is in `cycle_space_attack.md`: contracting a bridge
produces a smaller simple graph of minimum degree at least three, while every
cycle in the resulting 1-sum lifts unchanged to one bridge side.
-/

namespace Statements.ErdosGyarfasBridgeElimination

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

/-- Minimum order is all that bridge contraction needs; no edge-count
tie-breaker is assumed. -/
def IsOrderMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    IsCex H → n ≤ m

/-- A minimum-order counterexample has no bridge. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsOrderMinCex G → ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

theorem target : statement := by
  sorry

end Statements.ErdosGyarfasBridgeElimination

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
Jig-ready canonical proposition for the bridge dichotomy in a
lexicographically minimum Erdős--Gyárfás counterexample.

This file only declares the proposition.  `BridgeDichotomyArithmetic.lean`
kernel-checks its numerical core, while `bridge_dichotomy.md` gives the full
graph-theoretic proof.
-/

namespace Statements.ErdosGyarfasBridgeDichotomy

open scoped Sym2

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

/-- The vertices reachable from `root` after deleting the proposed bridge. -/
def bridgeSide {n : ℕ} (G : SimpleGraph (Fin n)) (u v root : Fin n) : Set (Fin n) :=
  {w | (G.deleteEdges {s(u, v)}).Reachable root w}

/-- The component graph on one side of the proposed bridge. -/
def sideGraph {n : ℕ} (G : SimpleGraph (Fin n)) (u v root : Fin n) :
    SimpleGraph (bridgeSide G u v root) :=
  (G.deleteEdges {s(u, v)}).induce (bridgeSide G u v root)

/-- Any bridge in a lexicographically minimum counterexample is the unique
bridge.  Its endpoints are cubic, and deleting it produces two equal-order,
equal-size, bridgeless one-port blocks. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    ∀ u v : Fin n, G.Adj u v → G.IsBridge s(u, v) →
      G.degree u = 3 ∧ G.degree v = 3 ∧
      2 * Set.ncard (bridgeSide G u v u) = n ∧
      2 * Set.ncard (bridgeSide G u v v) = n ∧
      Set.ncard (sideGraph G u v u).edgeSet = Set.ncard (sideGraph G u v v).edgeSet ∧
      (∀ e ∈ (sideGraph G u v u).edgeSet, ¬(sideGraph G u v u).IsBridge e) ∧
      (∀ e ∈ (sideGraph G u v v).edgeSet, ¬(sideGraph G u v v).IsBridge e) ∧
      ∀ e ∈ G.edgeSet, G.IsBridge e → e = s(u, v)

theorem target : statement := by
  sorry

end Statements.ErdosGyarfasBridgeDichotomy

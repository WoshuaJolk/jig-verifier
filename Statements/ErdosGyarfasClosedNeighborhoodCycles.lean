import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasClosedNeighborhoodCycles

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ),
    c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsOrderMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    IsCex H → n ≤ m

/-- Every vertex of a minimum-order counterexample lies on a cycle whose
length is two more than a power of two. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsOrderMinCex G → ∀ v : Fin n,
      ∃ (w : Fin n) (c : G.Walk w w) (k : ℕ),
        c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k + 2 ∧ v ∈ c.support

theorem target : statement := by
  sorry

end Statements.ErdosGyarfasClosedNeighborhoodCycles

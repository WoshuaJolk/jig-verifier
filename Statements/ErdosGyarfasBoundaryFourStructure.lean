import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasBoundaryFourStructure

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

/-- At the first cubic-count boundary allowed by statement 9, every vertex of
degree at least four has degree exactly four. If there are at least two such
vertices, at most one cubic vertex has no neighbor of degree at least four. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    3 * (Finset.univ.filter fun v => G.degree v = 3).card = 2 * n + 4 →
      (∀ u : Fin n, 4 ≤ G.degree u → G.degree u = 4) ∧
        (2 ≤ (Finset.univ.filter fun v => 4 ≤ G.degree v).card →
          ((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
            ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v =>
              G.Adj v x).card = 0).card ≤ 1)

theorem target : statement := by sorry

end Statements.ErdosGyarfasBoundaryFourStructure

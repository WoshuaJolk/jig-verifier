import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Statements.ErdosGyarfasWeightedCubicBound

def HasPow2Cycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (v : Fin n) (c : G.Walk v v) (k : ℕ), c.IsCycle ∧ 2 ≤ k ∧ c.length = 2 ^ k

def IsCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  0 < n ∧ (∀ v : Fin n, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

def IsMinCex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  IsCex G ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], IsCex H →
    n < m ∨ (n = m ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

/-- A weighted cubic surplus bound with at least six vertices of degree >=4.
The surplus includes the high-degree excess and paired cubic vertices with no
high-degree neighbor. -/
abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsMinCex G →
    6 ≤ (Finset.univ.filter fun u => 4 ≤ G.degree u).card →
    2 * n + 6 +
      ((∑ u ∈ (Finset.univ.filter fun u => 4 ≤ G.degree u), G.degree u) -
        4 * (Finset.univ.filter fun u => 4 ≤ G.degree u).card) +
      2 * (((Finset.univ.filter fun x => G.degree x = 3).filter fun x =>
        ((Finset.univ.filter fun v => 4 ≤ G.degree v).filter fun v => G.Adj v x).card = 0).card / 2)
      ≤ 3 * (Finset.univ.filter fun x => G.degree x = 3).card

theorem target : statement := sorry

end Statements.ErdosGyarfasWeightedCubicBound

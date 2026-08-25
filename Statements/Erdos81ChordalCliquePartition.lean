import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped Sym2

namespace Statements.Erdos81ChordalCliquePartition

open SimpleGraph

def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (cycle : G.Walk v v), cycle.IsCycle → 4 ≤ cycle.length →
    ∃ x y : V, x ∈ cycle.support ∧ y ∈ cycle.support ∧
      G.Adj x y ∧ s(x, y) ∉ cycle.edges

def IsEdgeCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
  ∀ edge ∈ G.edgeFinset,
    ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

/-- Erdős Problem 81: every finite chordal graph has an edge-clique
partition of size at most `n²/6 + O(n)`. -/
abbrev statement : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    ∀ (_ : DecidableRel G.Adj), IsChordal G →
      ∃ parts : Finset (Finset (Fin n)),
        IsEdgeCliquePartition G parts ∧
        6 * parts.card ≤ n ^ 2 + C * n

theorem target : statement := sorry

end Statements.Erdos81ChordalCliquePartition

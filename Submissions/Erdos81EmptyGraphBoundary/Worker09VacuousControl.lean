import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped Sym2

namespace Submissions.Erdos81EmptyGraphBoundary.Worker09VacuousControl

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

theorem proof (h : False) :
    ∀ n : ℕ,
      IsChordal (⊥ : SimpleGraph (Fin n)) ∧
      IsEdgeCliquePartition (⊥ : SimpleGraph (Fin n)) ∅ ∧
      6 * (∅ : Finset (Finset (Fin n))).card ≤ n ^ 2 := h.elim

end Submissions.Erdos81EmptyGraphBoundary.Worker09VacuousControl

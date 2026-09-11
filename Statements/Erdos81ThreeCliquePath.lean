import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Statements.Erdos81ThreeCliquePath

open scoped Sym2
open Finset SimpleGraph

def IsEdgeCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
    ∀ edge ∈ G.edgeFinset,
      ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

abbrev statement : Prop := by
  classical
  exact ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ L M R : Finset (Fin n),
    G.IsClique (L : Set (Fin n)) → G.IsClique (M : Set (Fin n)) →
    G.IsClique (R : Set (Fin n)) → L ∩ R ⊆ M →
    (∀ e ∈ G.edgeFinset, e ∈ L.sym2 ∨ e ∈ M.sym2 ∨ e ∈ R.sym2) →
    ∃ parts : Finset (Finset (Fin n)), IsEdgeCliquePartition G parts ∧
      6 * parts.card ≤ n^2 + 18

end Statements.Erdos81ThreeCliquePath

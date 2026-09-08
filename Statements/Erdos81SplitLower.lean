import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped Sym2
open Finset SimpleGraph

namespace Statements.Erdos81SplitLower

def IsEdgeCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : Prop :=
  (∀ clique ∈ parts, G.IsClique (clique : Set V)) ∧
  ∀ edge ∈ G.edgeFinset,
    ∃! clique : Finset V, clique ∈ parts ∧ edge ∈ clique.sym2

def completeSplit (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := x ≠ y ∧ (x.isLeft ∨ y.isLeft)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (a b : ℕ) : DecidableRel (completeSplit a b).Adj :=
  inferInstanceAs (DecidableRel fun (x y : Fin a ⊕ Fin b) =>
    x ≠ y ∧ (x.isLeft ∨ y.isLeft))

/-- The classical complete-split lower obstruction, for every size parameter. -/
abbrev statement : Prop :=
  ∀ t : ℕ, ∀ parts : Finset (Finset (Fin t ⊕ Fin (2 * t))),
    IsEdgeCliquePartition (completeSplit t (2 * t)) parts →
      3 * t ^ 2 + t ≤ 2 * parts.card

theorem target : statement := sorry

end Statements.Erdos81SplitLower

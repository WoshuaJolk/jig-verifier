import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain

namespace Statements.Erdos583SingleEdgeDecomposition

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V,
    p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b →
    ∃! p : List V, p ∈ paths ∧ PathUses p a b

/-- The connected two-vertex graph attains Gallai's ceiling with its unique
edge as one path. -/
abbrev statement : Prop :=
  ∃ paths : Finset (List (Fin 2)),
    paths.card ≤ (2 + 1) / 2 ∧
    IsPathDecomposition (⊤ : SimpleGraph (Fin 2)) paths

theorem target : statement := sorry

end Statements.Erdos583SingleEdgeDecomposition

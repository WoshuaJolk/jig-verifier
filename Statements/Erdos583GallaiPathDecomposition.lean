import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain

namespace Statements.Erdos583GallaiPathDecomposition

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

/-- The Erdős--Gallai path-decomposition conjecture, Erdős Problem 583. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.Connected →
    ∃ paths : Finset (List (Fin n)),
      paths.card ≤ (n + 1) / 2 ∧ IsPathDecomposition G paths

theorem target : statement := sorry

end Statements.Erdos583GallaiPathDecomposition

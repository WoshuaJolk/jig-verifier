import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos583PathCapacity

def IsPath {V : Type} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.Chain' G.Adj

def PathUses {V : Type} (p : List V) (a b : V) : Prop :=
  ∃ l r : List V, p = l ++ a :: b :: r ∨ p = l ++ b :: a :: r

def IsPathDecomposition {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (paths : Finset (List V)) : Prop :=
  (∀ p ∈ paths, IsPath G p) ∧
  ∀ ⦃a b : V⦄, G.Adj a b → ∃! p : List V, p ∈ paths ∧ PathUses p a b

abbrev statement : Prop :=
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (paths : Finset (List (Fin n))),
      IsPathDecomposition G paths → Nat.card G.edgeSet ≤ paths.card * (n - 1)) ∧
    (∀ (k : ℕ) (G : SimpleGraph (Fin (2 * k + 1)))
      (paths : Finset (List (Fin (2 * k + 1)))),
      2 * k * k < Nat.card G.edgeSet → IsPathDecomposition G paths → k + 1 ≤ paths.card) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ paths : Finset (List (Fin (2 * k + 1))),
      IsPathDecomposition (⊤ : SimpleGraph (Fin (2 * k + 1))) paths → k + 1 ≤ paths.card)

theorem target : statement := sorry

end Statements.Erdos583PathCapacity

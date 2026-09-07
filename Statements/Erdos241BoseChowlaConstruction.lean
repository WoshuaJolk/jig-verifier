import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos241BoseChowlaConstruction

open Finset

noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/-- Finite prime-parameter consequence of the classical Bose–Chowla construction. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ maxUniqueSums (p ^ 3 - 2) 3

theorem target : statement := sorry

end Statements.Erdos241BoseChowlaConstruction

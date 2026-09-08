import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Statements.Erdos241BoseChowlaLowerAsymptotic

open Finset Filter

noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/-- Classical Bose–Chowla lower direction, extended to every large cutoff using PNT. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (maxUniqueSums N 3 : ℝ)

theorem target : statement := sorry

end Statements.Erdos241BoseChowlaLowerAsymptotic

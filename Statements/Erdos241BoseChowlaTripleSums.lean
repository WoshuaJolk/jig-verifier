import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos241BoseChowlaTripleSums

open Filter Finset
open scoped Asymptotics

/-- Maximum cardinality of a subset of `{1, ..., N}` with unique
`r`-term sums, modulo permutation of summands. -/
noncomputable def maxUniqueSums (N r : ℕ) : ℕ :=
  open scoped Classical in
  let candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/-- Erdős Problem 241, the order-three Bose–Chowla conjecture. -/
abbrev statement : Prop :=
  (fun N ↦ (maxUniqueSums N 3 : ℝ)) ~[atTop]
    (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))

theorem target : statement := sorry

end Statements.Erdos241BoseChowlaTripleSums

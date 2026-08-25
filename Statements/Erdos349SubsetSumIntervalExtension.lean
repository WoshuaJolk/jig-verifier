import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos349SubsetSumIntervalExtension

open Finset

/-- The overlap engine behind completeness arguments: if subset sums of
`values` cover `[0,L]`, adjoining a fresh value at most `L+1` extends coverage
through `L+a`. -/
abbrev statement : Prop :=
  ∀ (values : Finset ℕ) (a L : ℕ), a ∉ values →
    (∀ n ≤ L, ∃ chosen : Finset ℕ, chosen ⊆ values ∧ ∑ x ∈ chosen, x = n) →
    a ≤ L + 1 →
    ∀ n ≤ L + a, ∃ chosen : Finset ℕ,
      chosen ⊆ insert a values ∧ ∑ x ∈ chosen, x = n

theorem target : statement := sorry

end Statements.Erdos349SubsetSumIntervalExtension

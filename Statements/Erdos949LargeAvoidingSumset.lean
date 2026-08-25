import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

namespace Statements.Erdos949LargeAvoidingSumset

open Cardinal
open scoped Pointwise

/-- Erdős Problem 949: every sum-free subset of the reals has a
continuum-sized subset of its complement whose pairwise sums also avoid it. -/
abbrev statement : Prop :=
  ∀ S : Set ℝ, (∀ a ∈ S, ∀ b ∈ S, a + b ∉ S) →
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ

theorem target : statement := sorry

end Statements.Erdos949LargeAvoidingSumset

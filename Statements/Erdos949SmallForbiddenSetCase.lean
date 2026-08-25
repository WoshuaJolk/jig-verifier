import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

namespace Statements.Erdos949SmallForbiddenSetCase

open Cardinal
open scoped Pointwise

/-- The cardinal-small case of Erdős Problem 949 does not need sum-freeness:
every forbidden set smaller than the continuum admits a continuum-sized
avoiding set whose pairwise sums also avoid it. -/
abbrev statement : Prop :=
  ∀ S : Set ℝ, #S < 𝔠 →
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ

theorem target : statement := sorry

end Statements.Erdos949SmallForbiddenSetCase

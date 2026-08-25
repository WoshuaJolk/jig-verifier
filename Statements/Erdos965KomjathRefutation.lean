import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable

namespace Statements.Erdos965KomjathRefutation

/-- Komjáth's ZFC negative resolution of Erdős Problem 965: there is a
two-colouring of the reals for which no uncountable set has all sums of
distinct pairs in one colour. -/
abbrev statement : Prop :=
  ¬ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A),
        a ≠ b → c ≠ d → f (a + b) = f (c + d)

theorem target : statement := by
  sorry

end Statements.Erdos965KomjathRefutation

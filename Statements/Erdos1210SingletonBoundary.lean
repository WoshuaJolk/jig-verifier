import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting

open Finset

namespace Statements.Erdos1210SingletonBoundary

/-- The corrected Erdős 1210 inequality with absolute constant one for admissible families having at most one member. -/
abbrev statement : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a < n) →
    A.card ≤ 1 →
      ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
        (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + 1

theorem target : statement := sorry

end Statements.Erdos1210SingletonBoundary

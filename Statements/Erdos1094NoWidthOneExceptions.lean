import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos1094NoWidthOneExceptions

/-- The complete `k=1` slice of Erdős Problem 1094 has no exceptions. -/
abbrev statement : Prop :=
  ∀ n : ℕ,
    ¬(0 < 1 ∧ 2 * 1 ≤ n ∧
      (n.choose 1).minFac > max (n / 1) 1)

theorem target : statement := sorry

end Statements.Erdos1094NoWidthOneExceptions

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos950PrimeReciprocalNonnegative

noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime,
    (1 : ℝ) / (n - p : ℝ)

/-- Every finite reciprocal-prime-distance sum is nonnegative. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 0 ≤ f n

theorem target : statement := sorry

end Statements.Erdos950PrimeReciprocalNonnegative

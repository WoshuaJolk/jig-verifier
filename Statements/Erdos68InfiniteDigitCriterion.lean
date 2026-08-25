import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Statements.Erdos68InfiniteDigitCriterion

noncomputable def factorialDigit (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋ -
    (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋

noncomputable def series : ℝ :=
  ∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)

/-- To prove the Erdős 68 series irrational, it suffices to show that its
canonical factorial digits are nonzero at arbitrarily large indices. -/
abbrev statement : Prop :=
  (∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ factorialDigit series m ≠ 0) →
    Irrational series

theorem target : statement := sorry

end Statements.Erdos68InfiniteDigitCriterion

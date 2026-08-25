import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Statements.Erdos68GeometricCarry

/-- After truncating the repeating base-`n!` expansion of `1 / (n! - 1)`
after `J` digits, the remainder is exactly known and lies strictly between one
and two units at the next base-`n!` position. -/
abbrev statement : Prop :=
  ∀ n J : ℕ, 3 ≤ n →
    let B : ℝ := n.factorial
    let R : ℝ :=
      1 / (B - 1) - ∑ j ∈ Finset.range J, 1 / B ^ (j + 1)
    R = 1 / (B ^ J * (B - 1)) ∧
      1 / B ^ (J + 1) < R ∧
      R < 2 / B ^ (J + 1)

theorem target : statement := sorry

end Statements.Erdos68GeometricCarry

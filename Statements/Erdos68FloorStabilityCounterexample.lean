import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos68FloorStabilityCounterexample

/-- Although the first omitted contribution scaled by `4!` is below one, it
already changes the floor of the scaled finite sum. -/
abbrev statement : Prop :=
  let S4 : ℝ :=
    1 / ((2 : ℕ).factorial - 1 : ℕ) +
    1 / ((3 : ℕ).factorial - 1 : ℕ) +
    1 / ((4 : ℕ).factorial - 1 : ℕ)
  let t : ℝ :=
    (4 : ℕ).factorial / ((5 : ℕ).factorial - 1 : ℕ)
  ⌊((4 : ℕ).factorial : ℝ) * S4⌋ = 29 ∧
    ⌊((4 : ℕ).factorial : ℝ) * S4 + t⌋ = 30 ∧
    0 < t ∧ t < 1

theorem target : statement := sorry

end Statements.Erdos68FloorStabilityCounterexample

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68FloorStabilityCounterexample.FloorStabilityCounterexample

/-- Although the first omitted contribution scaled by `4!` is below one, it
already changes the floor of the scaled finite sum. -/
theorem proof :
    let S4 : ℝ :=
      1 / ((2 : ℕ).factorial - 1 : ℕ) +
      1 / ((3 : ℕ).factorial - 1 : ℕ) +
      1 / ((4 : ℕ).factorial - 1 : ℕ)
    let t : ℝ :=
      (4 : ℕ).factorial / ((5 : ℕ).factorial - 1 : ℕ)
    ⌊((4 : ℕ).factorial : ℝ) * S4⌋ = 29 ∧
      ⌊((4 : ℕ).factorial : ℝ) * S4 + t⌋ = 30 ∧
      0 < t ∧ t < 1 := by
  norm_num [Nat.factorial, Int.floor]

end Submissions.Erdos68FloorStabilityCounterexample.FloorStabilityCounterexample

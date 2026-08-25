import Mathlib

namespace Submissions.Erdos16PrimePowerAPDensity.Control

open Filter Nat Set
open scoped Classical Topology

/-- Must-fail anti-restatement control: it assumes the complete canonical
refutation before returning it. -/
theorem proof :
    (¬ ∃ A B : Set ℕ,
      {n : ℕ | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p} = A ∪ B ∧
      (∃ a d : ℕ, d > 0 ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧
      Tendsto (fun x : ℕ => (count (· ∈ B) x : ℝ) / (x : ℝ))
        atTop (𝓝 0)) →
    ¬ ∃ A B : Set ℕ,
      {n : ℕ | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p} = A ∪ B ∧
      (∃ a d : ℕ, d > 0 ∧ A = {x | ∃ m : ℕ, x = a + m * d}) ∧
      Tendsto (fun x : ℕ => (count (· ∈ B) x : ℝ) / (x : ℝ))
        atTop (𝓝 0) := by
  exact id

end Submissions.Erdos16PrimePowerAPDensity.Control

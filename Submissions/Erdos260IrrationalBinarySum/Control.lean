import Mathlib

namespace Submissions.Erdos260IrrationalBinarySum.Control

theorem proof :
    ∀ a : ℕ → ℤ, ∀ s : ℝ,
      StrictMono a →
      Filter.Tendsto (fun n => (a n : ℝ) / n) Filter.atTop Filter.atTop →
      HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
      Irrational s →
      Irrational s := by
  aesop

end Submissions.Erdos260IrrationalBinarySum.Control

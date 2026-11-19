import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Submissions.Erdos647HoldsAtTwentyFour.HalfOnly

/-- Degenerate control: only the first conjunct. Must not be accepted. -/
theorem proof : ∀ m : ℕ, m < 24 → m + m.divisors.card ≤ 24 + 2 := by decide

end Submissions.Erdos647HoldsAtTwentyFour.HalfOnly

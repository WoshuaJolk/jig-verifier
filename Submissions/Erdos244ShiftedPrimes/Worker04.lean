import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos244ShiftedPrimes.Worker04

def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

theorem proof : ∀ C : ℝ, ∀ p : ℕ, p.Prime → p + 1 ∈ representable C := by
  intro C p hp
  refine ⟨p, 0, hp, ?_⟩
  norm_num

end Submissions.Erdos244ShiftedPrimes.Worker04

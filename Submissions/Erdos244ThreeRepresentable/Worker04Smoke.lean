import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos244ThreeRepresentable.Worker04Smoke

def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

theorem proof : 3 ∈ representable 2 := by
  refine ⟨2, 0, Nat.prime_two, ?_⟩
  norm_num

end Submissions.Erdos244ThreeRepresentable.Worker04Smoke

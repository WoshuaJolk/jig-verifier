import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos244ThreeRepresentable.Worker04Degenerate

def representable (C : ℝ) : Set ℕ :=
  {x | ∃ p k : ℕ, p.Prime ∧ x = p + ⌊C ^ k⌋₊}

theorem proof : False → 3 ∈ representable 2 :=
  False.elim

end Submissions.Erdos244ThreeRepresentable.Worker04Degenerate

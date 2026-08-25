import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

namespace Submissions.Erdos873ZeroWindowInfinite.Worker09Upper

def blockLCM (a : ℕ → ℕ) (i k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun j => a (i + j))

noncomputable def windowCount (a : ℕ → ℕ) (X : ℝ) (k : ℕ) : ℕ∞ :=
  {i : ℕ | (blockLCM a i k : ℝ) < X}.encard

theorem proof : ∀ a : ℕ → ℕ, windowCount a 2 0 = ⊤ := by
  intro a
  simp [windowCount, blockLCM]

end Submissions.Erdos873ZeroWindowInfinite.Worker09Upper

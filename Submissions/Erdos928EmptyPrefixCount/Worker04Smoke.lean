import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

open Finset

namespace Submissions.Erdos928EmptyPrefixCount.Worker04Smoke

noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ p ∣ n}

def smoothPair (α β : ℝ) (n : ℕ) : Prop :=
  (largestPrimeFactor n : ℝ) < (n : ℝ) ^ α ∧
    (largestPrimeFactor (n + 1) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β

noncomputable def smoothCount (α β : ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter (smoothPair α β)).card

theorem proof : ∀ α β : ℝ, smoothCount α β 0 = 0 := by
  simp [smoothCount]

end Submissions.Erdos928EmptyPrefixCount.Worker04Smoke

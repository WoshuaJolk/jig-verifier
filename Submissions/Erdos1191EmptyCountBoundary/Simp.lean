import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic

namespace Submissions.Erdos1191EmptyCountBoundary.Simp

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 n).ncard

noncomputable def normalizedCount (A : Set ℕ) (n : ℕ) : ℝ :=
  (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n)

theorem proof :
    ∀ n : ℕ, countUpTo ∅ n = 0 ∧ normalizedCount ∅ n = 0 := by
  intro n
  simp [countUpTo, normalizedCount]

end Submissions.Erdos1191EmptyCountBoundary.Simp

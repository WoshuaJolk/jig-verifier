import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card.Arithmetic

namespace Statements.Erdos1191EmptyCountBoundary

noncomputable def countUpTo (A : Set ℕ) (n : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 n).ncard

noncomputable def normalizedCount (A : Set ℕ) (n : ℕ) : ℝ :=
  (countUpTo A n : ℝ) / Real.sqrt n * Real.sqrt (Real.log n)

abbrev statement : Prop :=
  ∀ n : ℕ, countUpTo ∅ n = 0 ∧ normalizedCount ∅ n = 0

theorem target : statement := sorry

end Statements.Erdos1191EmptyCountBoundary

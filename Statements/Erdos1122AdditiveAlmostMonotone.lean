import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

namespace Statements.Erdos1122AdditiveAlmostMonotone

/-- Additivity on the positive integers for coprime arguments. -/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    f (a * b) = f a + f b

/-- The number of decreases of `f` between 1 and `X`. -/
noncomputable def decreaseCount (f : ℕ → ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => f (n + 1) < f n).card

def HasZeroDecreaseDensity (f : ℕ → ℝ) : Prop :=
  Tendsto (fun X : ℕ => (decreaseCount f X : ℝ) / (X : ℝ))
    atTop (nhds 0)

/-- Erdős 1122: an additive function that decreases only on a density-zero
set is a constant multiple of the logarithm. -/
abbrev statement : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → HasZeroDecreaseDensity f →
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → f n = c * Real.log n

theorem target : statement := sorry

end Statements.Erdos1122AdditiveAlmostMonotone

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

namespace Statements.Erdos517SquareExponentsFabry

open Filter

def squareExponents (k : ℕ) : ℕ := k * k

def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k ↦ n k / (k : ℝ)) atTop atTop

/-- Quadratic exponents satisfy the exact Fabry-gap hypothesis used by
Erdős Problem 517. -/
abbrev statement : Prop :=
  HasFabryGaps squareExponents

theorem target : statement := sorry

end Statements.Erdos517SquareExponentsFabry

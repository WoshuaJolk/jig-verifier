import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Statements.Erdos265RationalAhmesCriticalGrowth

open Filter

def HasRationalShiftedSums (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (∀ n, 2 ≤ a n) ∧
  Summable (fun n ↦ ((a n : ℝ))⁻¹) ∧
  Summable (fun n ↦ (((a n - 1 : ℕ) : ℝ))⁻¹) ∧
  (∃ q : ℚ, ∑' n, ((a n : ℝ))⁻¹ = (q : ℝ)) ∧
  ∃ r : ℚ, ∑' n, (((a n - 1 : ℕ) : ℝ))⁻¹ = (r : ℝ)

def ExceedsCriticalDoubleExponentialRate (a : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 1 < c ∧
    ∃ᶠ n : ℕ in atTop,
      c < Real.rpow (a n : ℝ) (((2 ^ n : ℕ) : ℝ)⁻¹)

/-- The remaining open branch of Erdős Problem 265: rationality of both
shifted Ahmes series is compatible with limsup `a_n^(1/2^n) > 1`. -/
abbrev statement : Prop :=
  ∃ a : ℕ → ℕ,
    HasRationalShiftedSums a ∧ ExceedsCriticalDoubleExponentialRate a

theorem target : statement := sorry

end Statements.Erdos265RationalAhmesCriticalGrowth

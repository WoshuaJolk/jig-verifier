import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos445ExponentMonotonicity

def HasInversePair (c : ℝ) (p n : ℕ) : Prop :=
  ∃ a b : ℕ,
    n < a ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    n < b ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p]

/-- Increasing the interval exponent preserves every reciprocal-pair
witness when the modulus is at least one. -/
abbrev statement : Prop :=
  ∀ c d : ℝ, ∀ p n : ℕ, c ≤ d → 1 ≤ p →
    HasInversePair c p n → HasInversePair d p n

theorem target : statement := sorry

end Statements.Erdos445ExponentMonotonicity

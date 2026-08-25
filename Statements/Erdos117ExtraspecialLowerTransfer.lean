import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter

namespace Statements.Erdos117ExtraspecialLowerTransfer

/-- Arithmetic/asymptotic transfer for the extraspecial lower construction:
odd-index powers of two plus monotonicity imply the eventual constant-loss
base-two logarithmic lower bound. -/
abbrev statement : Prop :=
  ∀ (h : ℕ → ℕ),
    Monotone h →
    (∀ m : ℕ, 2 ^ m ≤ h (2 * m + 1)) →
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 2 - 1 ≤ Real.logb 2 (h n : ℝ)

theorem target : statement := sorry

end Statements.Erdos117ExtraspecialLowerTransfer

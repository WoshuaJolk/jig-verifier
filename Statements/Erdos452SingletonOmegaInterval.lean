import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Statements.Erdos452SingletonOmegaInterval

def omega (n : ℕ) : ℕ := n.primeFactorsList.length

def HasOmegaRichInterval (x k : ℕ) : Prop :=
  ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x + 1 ∧
    (Real.log (x : ℝ)) ^ k ≤ L ∧
      ∀ n : ℕ, a ≤ n → n < a + L →
        Real.log (Real.log (n : ℝ)) < omega n

/-- The singleton interval `{3}` is omega-rich at exponent zero. -/
abbrev statement : Prop := HasOmegaRichInterval 3 0

theorem target : statement := sorry

end Statements.Erdos452SingletonOmegaInterval

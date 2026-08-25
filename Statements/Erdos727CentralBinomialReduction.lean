import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos727CentralBinomialReduction

/-- The factorial-square condition in Erdős Problem 727 is exactly a
divisibility condition on a central binomial coefficient and a rising
factorial. -/
abbrev statement : Prop :=
  ∀ n k : ℕ,
    (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n) ↔
      ((n + 1).ascFactorial k) ^ 2 ∣ Nat.choose (2 * n) n

theorem target : statement := sorry

end Statements.Erdos727CentralBinomialReduction

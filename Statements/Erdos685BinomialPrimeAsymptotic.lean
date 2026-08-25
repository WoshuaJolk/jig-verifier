import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos685BinomialPrimeAsymptotic

open Filter

noncomputable def primeDivisorCount (n k : ℕ) : ℕ :=
  (Nat.choose n k).primeFactors.card

noncomputable def predictedCount (n k : ℕ) : ℝ :=
  (k : ℝ) * ∑ p ∈ (Finset.Ioo k n).filter Nat.Prime, (p : ℝ)⁻¹

/-- Erdős Problem 685: uniformly for `n^ε < k ≤ n^(1-ε)`, the number
of distinct prime divisors of `n.choose k` has the predicted asymptotic. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ k : ℕ, (n : ℝ) ^ ε < k → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
      |(primeDivisorCount n k : ℝ) - predictedCount n k| ≤
        δ * predictedCount n k

theorem target : statement := sorry

end Statements.Erdos685BinomialPrimeAsymptotic

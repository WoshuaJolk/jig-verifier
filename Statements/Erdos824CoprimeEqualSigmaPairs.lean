import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace Statements.Erdos824CoprimeEqualSigmaPairs

open Filter
open scoped BigOperators

def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def pairCount (x : ℕ) : ℕ :=
  ((Finset.range x) ×ˢ (Finset.range x)).filter
    (fun ab => 1 ≤ ab.1 ∧ ab.1 < ab.2 ∧
      Nat.Coprime ab.1 ab.2 ∧ sigma ab.1 = sigma ab.2) |>.card

/-- Erdős problem 824: almost-quadratically many coprime equal-sigma pairs. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (2 - ε) < pairCount x

theorem target : statement := sorry

end Statements.Erdos824CoprimeEqualSigmaPairs

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped BigOperators

namespace Statements.Erdos935PowerfulPartConsecutiveProduct

noncomputable def powerfulPart (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => if 2 ≤ e then p ^ e else 1

def consecutiveProduct (n ℓ : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (ℓ + 1), (n + i)

/-- The three quantitative questions in Erdős 935. -/
abbrev statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ ℓ : ℕ, 1 ≤ ℓ →
    ∀ᶠ n : ℕ in atTop,
      (powerfulPart (consecutiveProduct n ℓ) : ℝ) <
        (n : ℝ) ^ (2 + ε)) ∧
  (∀ ℓ : ℕ, 2 ≤ ℓ →
    ∀ B : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      B < (powerfulPart (consecutiveProduct n ℓ) : ℝ) / (n : ℝ) ^ 2) ∧
  (∀ ℓ : ℕ, 2 ≤ ℓ →
    Tendsto
      (fun n : ℕ =>
        (powerfulPart (consecutiveProduct n ℓ) : ℝ) /
          (n : ℝ) ^ (ℓ + 1))
      atTop (nhds 0))

theorem target : statement := sorry

end Statements.Erdos935PowerfulPartConsecutiveProduct

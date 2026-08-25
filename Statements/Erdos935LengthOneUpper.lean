import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped BigOperators

namespace Statements.Erdos935LengthOneUpper

/-- The elementary `ℓ = 1` case of the first quantitative assertion in
Erdős 935. Definitions are local structural lets so a standalone proof can
inhabit the canonical proposition without importing this module. -/
abbrev statement : Prop :=
  let powerfulPart : ℕ → ℕ := fun n =>
    n.factorization.prod fun p e => if 2 ≤ e then p ^ e else 1
  let consecutiveProduct : ℕ → ℕ → ℕ := fun n ℓ =>
    ∏ i ∈ Finset.range (ℓ + 1), (n + i)
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (powerfulPart (consecutiveProduct n 1) : ℝ) <
        (n : ℝ) ^ (2 + ε)

theorem target : statement := sorry

end Statements.Erdos935LengthOneUpper

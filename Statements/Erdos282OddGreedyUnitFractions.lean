import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos282OddGreedyUnitFractions

open Filter

noncomputable def greedyUnitFractionRem (A : Set ℕ) (x : ℚ) : ℕ → ℚ
  | 0 => x - 1 / sInf {n | n ∈ A ∧ 1 / x ≤ n}
  | t + 1 =>
    let prev := greedyUnitFractionRem A x t
    if prev ≤ 0 then 0
    else prev - 1 / sInf {n | n ∈ A ∧ 1 / prev ≤ n}

/-- Erdős problem 282: the odd-denominator greedy Egyptian-fraction
algorithm terminates for every rational in `(0,1)` with odd denominator. -/
abbrev statement : Prop :=
  ∀ x : ℚ, x ∈ Set.Ioo 0 1 → Odd x.den →
    greedyUnitFractionRem {n | Odd n} x =ᶠ[atTop] 0

theorem target : statement := sorry

end Statements.Erdos282OddGreedyUnitFractions

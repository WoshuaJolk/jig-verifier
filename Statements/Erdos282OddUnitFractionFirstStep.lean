import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos282OddUnitFractionFirstStep

/-- For an odd unit fraction `1/n`, the odd greedy rule selects `n` itself
and therefore leaves zero remainder in its first step. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 1 < n → Odd n →
    let chosen :=
      sInf {m : ℕ | Odd m ∧ (1 : ℚ) / (1 / (n : ℚ)) ≤ m}
    chosen = n ∧ (1 / (n : ℚ)) - 1 / (chosen : ℚ) = 0

theorem target : statement := sorry

end Statements.Erdos282OddUnitFractionFirstStep

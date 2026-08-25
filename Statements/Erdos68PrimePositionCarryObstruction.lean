import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

namespace Statements.Erdos68PrimePositionCarryObstruction

/-- At every prime factorial position `m ≥ 5`, a single term from the `n = 3`
geometric row is assigned to a higher raw position but is already larger than
one full `1 / m!` unit. Thus the unnormalized higher-position tail cannot be
bounded below one unit at `m`. -/
abbrev statement : Prop :=
  ∀ m : ℕ, m.Prime → 5 ≤ m →
    let j := m / 3 + 1
    m < 3 * j ∧
      (1 : ℝ) / m.factorial < 1 / (6 : ℝ) ^ j

theorem target : statement := sorry

end Statements.Erdos68PrimePositionCarryObstruction

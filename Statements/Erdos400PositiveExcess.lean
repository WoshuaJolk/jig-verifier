import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Lattice.Nat

open Finset

namespace Statements.Erdos400PositiveExcess

noncomputable def g (k n : ℕ) : ℕ :=
  sSup {x | ∃ a : Fin k → ℕ,
    (∏ i, Nat.factorial (a i)) ∣ Nat.factorial n ∧ x = (∑ i, a i) - n}

/-- The factorial-packing excess is positive whenever at least two slots are available. -/
abbrev statement : Prop :=
  ∀ k n : ℕ, 2 ≤ k → 0 < g k n

theorem target : statement := sorry

end Statements.Erdos400PositiveExcess

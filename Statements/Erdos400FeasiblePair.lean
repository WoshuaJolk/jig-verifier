import Mathlib.Data.Nat.Factorial.BigOperators

namespace Statements.Erdos400FeasiblePair

/-- Two ones are feasible for the factorial-packing problem at zero. -/
abbrev statement : Prop :=
  ∃ a : Fin 2 → ℕ,
    (∏ i, Nat.factorial (a i)) ∣ Nat.factorial 0 ∧
    (∑ i, a i) = 2

theorem target : statement := sorry

end Statements.Erdos400FeasiblePair

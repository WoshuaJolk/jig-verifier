import Mathlib.Data.Nat.Totient

namespace Statements.Erdos694UniqueTotientDivisibleByFour

/-- Any unique positive preimage of Euler's totient function must be divisible by four. -/
abbrev statement : Prop :=
  ∀ n > 0, (∃! m : ℕ, Nat.totient m = n) →
    ∃ m : ℕ, Nat.totient m = n ∧ 4 ∣ m

theorem target : statement := sorry

end Statements.Erdos694UniqueTotientDivisibleByFour

import Mathlib.Data.Nat.Totient

namespace Statements.Erdos694UniqueTotientValue

/-- The open Carmichael variant attached to Erdős Problem 694: some positive totient value has exactly one preimage. -/
abbrev statement : Prop :=
  ∃ n > 0, ∃! m : ℕ, Nat.totient m = n

theorem target : statement := sorry

end Statements.Erdos694UniqueTotientValue

import Mathlib.Data.Nat.GCD.Basic

namespace Statements.Erdos820ExponentThreeCoprime

/-- Exponent three is an explicit coprime witness. -/
abbrev statement : Prop :=
  Nat.Coprime (2 ^ 3 - 1) (3 ^ 3 - 1)

theorem target : statement := sorry

end Statements.Erdos820ExponentThreeCoprime

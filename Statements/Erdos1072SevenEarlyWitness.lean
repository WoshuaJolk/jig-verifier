import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq

namespace Statements.Erdos1072SevenEarlyWitness

/-- Three factorial already equals minus one modulo seven. -/
abbrev statement : Prop :=
  (3 : ℕ).factorial + 1 ≡ 0 [MOD 7]

theorem target : statement := sorry

end Statements.Erdos1072SevenEarlyWitness

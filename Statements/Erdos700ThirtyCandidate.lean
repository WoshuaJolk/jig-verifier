import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos700ThirtyCandidate

/-- The index five gives the value six in the defining minimum for `f(30)`. -/
abbrev statement : Prop :=
  Nat.gcd 30 ((30 : ℕ).choose 5) = 6

theorem target : statement := sorry

end Statements.Erdos700ThirtyCandidate

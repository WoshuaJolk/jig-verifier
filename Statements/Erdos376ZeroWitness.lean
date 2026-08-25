import Mathlib.Data.Nat.Choose.Central

namespace Statements.Erdos376ZeroWitness

/-- The zero index is a coprime central-binomial witness. -/
abbrev statement : Prop :=
  (0 : ℕ).centralBinom.Coprime 105

theorem target : statement := sorry

end Statements.Erdos376ZeroWitness

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Basic

namespace Statements.Erdos1003FourWitnesses

/-- Four explicit starts with equal consecutive totients. -/
abbrev statement : Prop :=
  ∀ n ∈ ({1, 3, 15, 104} : Finset ℕ),
    Nat.totient n = Nat.totient (n + 1)

theorem target : statement := sorry

end Statements.Erdos1003FourWitnesses

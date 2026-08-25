import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic

namespace Statements.Erdos879SingletonAdmissible

def Admissible (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

abbrev statement : Prop :=
  Admissible {1}

theorem target : statement := sorry

end Statements.Erdos879SingletonAdmissible

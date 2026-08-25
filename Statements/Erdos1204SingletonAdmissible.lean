import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open Finset

namespace Statements.Erdos1204SingletonAdmissible

def IsAdmissible (s : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ∃ r : ℕ, r < p ∧ ∀ a ∈ s, a % p ≠ r

/-- The singleton zero sequence is admissible. -/
abbrev statement : Prop :=
  IsAdmissible {0}

theorem target : statement := sorry

end Statements.Erdos1204SingletonAdmissible

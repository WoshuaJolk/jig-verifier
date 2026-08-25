import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos11FermatFormFamily

/-- Every number one greater than a positive power of two has the required
representation, with squarefree summand one. -/
abbrev statement : Prop :=
  ∀ l : ℕ, 0 < l →
    ∃ k m : ℕ, Squarefree k ∧ 2 ^ l + 1 = k + 2 ^ m

theorem target : statement := sorry

end Statements.Erdos11FermatFormFamily

import Mathlib.Data.Rat.Lemmas

namespace Statements.Erdos571RationalDomain

abbrev statement : Prop :=
  (1 : ℚ) ≤ 1 ∧ (1 : ℚ) < 2

theorem target : statement := sorry

end Statements.Erdos571RationalDomain

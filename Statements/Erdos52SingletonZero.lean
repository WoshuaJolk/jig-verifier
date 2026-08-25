import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Statements.Erdos52SingletonZero

/-- The singleton `{0}` has one sum and one product. -/
abbrev statement : Prop :=
  max (({0} : Finset ℤ) + {0}).card (({0} : Finset ℤ) * {0}).card = 1

theorem target : statement := sorry

end Statements.Erdos52SingletonZero

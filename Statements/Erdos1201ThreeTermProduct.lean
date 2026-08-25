import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1201ThreeTermProduct

abbrev statement : Prop :=
  (∏ i ∈ Finset.range (2 + 1), (5 + i)) = 210

theorem target : statement := sorry

end Statements.Erdos1201ThreeTermProduct

import Mathlib.FieldTheory.Finite.Basic

namespace Statements.Erdos985ThreeHasPrimePrimitiveRoot

/-- The first odd prime modulus satisfies Erdős 985, witnessed by `q=2`. -/
abbrev statement : Prop :=
  ∃ q : ℕ, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 3 - 1

theorem target : statement := sorry

end Statements.Erdos985ThreeHasPrimePrimitiveRoot

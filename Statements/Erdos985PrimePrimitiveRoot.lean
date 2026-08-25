import Mathlib.FieldTheory.Finite.Basic

namespace Statements.Erdos985PrimePrimitiveRoot

/-- Erdős Problem 985: every odd prime modulus has a smaller prime
which is a primitive root modulo it. -/
abbrev statement : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

theorem target : statement := sorry

end Statements.Erdos985PrimePrimitiveRoot

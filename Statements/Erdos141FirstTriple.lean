import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Statements.Erdos141FirstTriple

/-- `3,5,7` are consecutive primes and a nondegenerate
three-term arithmetic progression. -/
abbrev statement : Prop :=
  Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧
  3 + 2 = 5 ∧ 5 + 2 = 7 ∧
  ∀ p : ℕ, 3 ≤ p → p ≤ 7 →
    (Nat.Prime p ↔ p = 3 ∨ p = 5 ∨ p = 7)

theorem target : statement := sorry

end Statements.Erdos141FirstTriple

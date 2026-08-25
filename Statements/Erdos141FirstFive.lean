import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Statements.Erdos141FirstFive

/-- The smallest known five-term arithmetic progression of consecutive primes. -/
abbrev statement : Prop :=
  Nat.Prime 9843019 ∧
  Nat.Prime 9843049 ∧
  Nat.Prime 9843079 ∧
  Nat.Prime 9843109 ∧
  Nat.Prime 9843139 ∧
  9843019 + 30 = 9843049 ∧
  9843049 + 30 = 9843079 ∧
  9843079 + 30 = 9843109 ∧
  9843109 + 30 = 9843139 ∧
  ∀ p : ℕ, 9843019 ≤ p → p ≤ 9843139 →
    (Nat.Prime p ↔
      p = 9843019 ∨ p = 9843049 ∨ p = 9843079 ∨
      p = 9843109 ∨ p = 9843139)

theorem target : statement := sorry

end Statements.Erdos141FirstFive

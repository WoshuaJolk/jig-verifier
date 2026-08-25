import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Statements.Erdos141FirstFour

/-- `251,257,263,269` are four consecutive primes in a nondegenerate
arithmetic progression. -/
abbrev statement : Prop :=
  Nat.Prime 251 ∧ Nat.Prime 257 ∧ Nat.Prime 263 ∧ Nat.Prime 269 ∧
  251 + 6 = 257 ∧ 257 + 6 = 263 ∧ 263 + 6 = 269 ∧
  ∀ p : ℕ, 251 ≤ p → p ≤ 269 →
    (Nat.Prime p ↔ p = 251 ∨ p = 257 ∨ p = 263 ∨ p = 269)

theorem target : statement := sorry

end Statements.Erdos141FirstFour

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Submissions.Erdos141FirstFour.Worker09Control

theorem proof
    (claim :
      Nat.Prime 251 ∧ Nat.Prime 257 ∧ Nat.Prime 263 ∧ Nat.Prime 269 ∧
      251 + 6 = 257 ∧ 257 + 6 = 263 ∧ 263 + 6 = 269 ∧
      ∀ p : ℕ, 251 ≤ p → p ≤ 269 →
        (Nat.Prime p ↔ p = 251 ∨ p = 257 ∨ p = 263 ∨ p = 269)) :
    Nat.Prime 251 ∧ Nat.Prime 257 ∧ Nat.Prime 263 ∧ Nat.Prime 269 ∧
    251 + 6 = 257 ∧ 257 + 6 = 263 ∧ 263 + 6 = 269 ∧
    ∀ p : ℕ, 251 ≤ p → p ≤ 269 →
      (Nat.Prime p ↔ p = 251 ∨ p = 257 ∨ p = 263 ∨ p = 269) :=
  claim

end Submissions.Erdos141FirstFour.Worker09Control

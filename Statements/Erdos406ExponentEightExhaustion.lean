import Mathlib.Data.Nat.Digits.Lemmas

namespace Statements.Erdos406ExponentEightExhaustion

/-- Through exponent eight, exactly exponents 0, 2, and 8 give powers of two whose ternary expansions use only zero and one. -/
abbrev statement : Prop :=
  ∀ k ≤ 8,
    Nat.digits 3 (2 ^ k) ⊆ [0, 1] ↔ k = 0 ∨ k = 2 ∨ k = 8

theorem target : statement := sorry

end Statements.Erdos406ExponentEightExhaustion

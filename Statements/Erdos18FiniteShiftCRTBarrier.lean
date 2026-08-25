import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.PrimeCounting

namespace Statements.Erdos18FiniteShiftCRTBarrier

/-- CRT creates arbitrarily long consecutive gaps containing no divisors of
`k!`: each shifted value has its own prime divisor larger than `k`. -/
abbrev statement : Prop :=
  ∀ k h : ℕ, ∃ A : ℕ, h ≤ A ∧
    ∀ i : ℕ, i < h →
      ∃ p : ℕ,
        p.Prime ∧
        k < p ∧
        p ∣ A - i ∧
        ¬(A - i ∣ k.factorial)

theorem target : statement := sorry

end Statements.Erdos18FiniteShiftCRTBarrier

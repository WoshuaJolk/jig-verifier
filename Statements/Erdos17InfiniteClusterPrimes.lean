import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos17InfiniteClusterPrimes

def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    ∀ n : ℕ, Even n → (n : ℤ) ≤ (p : ℤ) - 3 →
      ∃ q₁ q₂ : ℕ,
        q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧
          (n : ℤ) = (q₁ : ℤ) - q₂

/-- Erdős Problem 17: there are infinitely many cluster primes. -/
abbrev statement : Prop :=
  Set.Infinite {p : ℕ | IsClusterPrime p}

theorem target : statement := sorry

end Statements.Erdos17InfiniteClusterPrimes

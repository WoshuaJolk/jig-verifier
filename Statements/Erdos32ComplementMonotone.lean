import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

namespace Statements.Erdos32ComplementMonotone

open Filter Set

def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

/-- Supersets of additive complements to the primes remain additive complements. -/
abbrev statement : Prop :=
  ∀ A B : Set ℕ, A ⊆ B →
    IsAdditiveComplementToPrimes A → IsAdditiveComplementToPrimes B

theorem target : statement := sorry

end Statements.Erdos32ComplementMonotone

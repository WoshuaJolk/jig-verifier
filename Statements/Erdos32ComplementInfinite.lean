import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

namespace Statements.Erdos32ComplementInfinite

open Filter Set

def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ p, p.Prime ∧ ∃ a ∈ A, n = p + a

/-- Every additive complement to the primes is infinite. -/
abbrev statement : Prop :=
  ∀ A : Set ℕ, IsAdditiveComplementToPrimes A → A.Infinite

theorem target : statement := sorry

end Statements.Erdos32ComplementInfinite

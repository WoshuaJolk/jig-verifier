import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos699BinomialGcdPrime

/-- Erdős Problem 699 (Erdős and Szekeres, 1978, Conjecture 1). For every
`1 ≤ i < j ≤ n / 2` the greatest prime factor of `gcd (C(n,i), C(n,j))` is at least `i`:
some prime `p ≥ i` divides both binomial coefficients. -/
abbrev statement : Prop :=
  ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
    ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)

theorem target : statement := sorry

end Statements.Erdos699BinomialGcdPrime

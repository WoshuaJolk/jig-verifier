import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos677PrimeInUpperBlock

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Erdős problem 677 holds for every pair of disjoint blocks whose upper block
contains a prime: if some prime `p` satisfies `m < p ≤ m + k`, then
`M(m,k) ≠ M(n,k)` whenever `n + k ≤ m`. -/
abbrev statement : Prop :=
  ∀ n m k p : ℕ, n + k ≤ m → p.Prime → m < p → p ≤ m + k →
    lcmInterval m k ≠ lcmInterval n k

theorem target : statement := sorry

end Statements.Erdos677PrimeInUpperBlock

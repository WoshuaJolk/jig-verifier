import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LcmQuadProduct

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Closed form for a block of four consecutive integers:
`2 * gcd(n+1,3) * lcm(n+1,...,n+4) = (n+1)(n+2)(n+3)(n+4)`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 2 * Nat.gcd (n + 1) 3 * lcmInterval n 4
      = (n + 1) * (n + 2) * (n + 3) * (n + 4)

theorem target : statement := sorry

end Statements.Erdos677LcmQuadProduct

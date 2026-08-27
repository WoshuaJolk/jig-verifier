import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos677LcmTripleProduct

/-- Least common multiple of `{n+1, ..., n+k}`, as in Erdős problem 677. -/
def lcmInterval (n k : ℕ) : ℕ :=
  (Finset.Ioc n (n + k)).lcm id

/-- Closed form for a block of three consecutive integers:
`gcd(n+1,2) * lcm(n+1,n+2,n+3) = (n+1)(n+2)(n+3)`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Nat.gcd (n + 1) 2 * lcmInterval n 3 = (n + 1) * (n + 2) * (n + 3)

theorem target : statement := sorry

end Statements.Erdos677LcmTripleProduct

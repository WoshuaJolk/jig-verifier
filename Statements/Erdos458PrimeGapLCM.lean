import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos458PrimeGapLCM

/-- The least common multiple of the integers in `[1,n]`. -/
def lcmUpto (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- Erdős--Graham's prime-gap LCM conjecture. `Nat.nth Nat.Prime` is
zero-indexed, so Lean index `k` represents the source prime `p_(k+1)`. -/
abbrev statement : Prop :=
  ∀ k : ℕ,
    lcmUpto ((k + 1).nth Nat.Prime - 1) <
      k.nth Nat.Prime * lcmUpto (k.nth Nat.Prime)

theorem target : statement := sorry

end Statements.Erdos458PrimeGapLCM

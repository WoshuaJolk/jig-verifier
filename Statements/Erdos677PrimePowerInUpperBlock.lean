import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos677PrimePowerInUpperBlock

def lcmInterval (n k : ℕ) : ℕ := (Finset.Ioc n (n + k)).lcm id

abbrev statement : Prop :=
  ∀ n m k p a : ℕ, n + k ≤ m → p.Prime → 0 < a →
    m < p ^ a → p ^ a ≤ m + k →
    lcmInterval m k ≠ lcmInterval n k

theorem target : statement := sorry

end Statements.Erdos677PrimePowerInUpperBlock

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Irrational

namespace Statements.Erdos251PrimeBinarySeries

/-- Erdős Problem 251: irrationality of the binary series formed from the
successive primes. -/
abbrev statement : Prop :=
  Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / (2 ^ n))

theorem target : statement := sorry

end Statements.Erdos251PrimeBinarySeries

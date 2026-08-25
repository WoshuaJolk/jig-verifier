import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Instances.Nat

open Nat Filter Finset
open scoped ArithmeticFunction.omega

namespace Statements.Erdos891PrimeFactorInterval

/-- Erdős Problem 891: every sufficiently late interval whose length
is the product of the first `k` primes contains an integer with more
than `k` distinct prime factors. -/
abbrev statement : Prop :=
  ∀ k ≥ 2, ∀ᶠ n : ℕ in atTop,
    ∃ m ∈ Ico n (n + ∏ i ∈ range k, i.nth Nat.Prime),
      k < ω m

theorem target : statement := sorry

end Statements.Erdos891PrimeFactorInterval

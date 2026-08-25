import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos1106PartitionPrimeFactorsLinear

open Filter Finset
open scoped BigOperators

def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

def cumulativePartitionProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Icc 1 n, partitionCount i

/-- Erdős Problem 1106(ii): eventually the product of the first `n`
partition numbers has more than `n` distinct prime factors. -/
abbrev statement : Prop :=
  ∀ᶠ n in atTop,
    (cumulativePartitionProduct n).primeFactors.card > n

theorem target : statement := sorry

end Statements.Erdos1106PartitionPrimeFactorsLinear

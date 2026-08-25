import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos1106PrimeFactorMonotonicity

open Finset
open scoped BigOperators

def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

def cumulativePartitionProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Icc 1 n, partitionCount i

/-- The distinct-prime-factor sets in Erdős Problem 1106 are monotone. -/
abbrev statement : Prop :=
  ∀ n : ℕ,
    (cumulativePartitionProduct n).primeFactors ⊆
      (cumulativePartitionProduct (n + 1)).primeFactors

theorem target : statement := sorry

end Statements.Erdos1106PrimeFactorMonotonicity

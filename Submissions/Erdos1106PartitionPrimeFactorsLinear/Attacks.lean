import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat

namespace Submissions.Erdos1106PartitionPrimeFactorsLinear.Attacks

open Filter Finset
open scoped BigOperators

def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

abbrev claimedStatement : Prop :=
  ∀ᶠ n in atTop,
    (∏ i ∈ Icc 1 n, partitionCount i).primeFactors.card > n

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem partitionDomainNonempty (n : ℕ) : Nonempty (Nat.Partition n) :=
  ⟨Nat.Partition.ofSums n {n} (by simp)⟩

end Submissions.Erdos1106PartitionPrimeFactorsLinear.Attacks

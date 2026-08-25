import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos1106PrimeFactorMonotonicity.Direct

open Finset
open scoped BigOperators

def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

def cumulativePartitionProduct (n : ℕ) : ℕ :=
  ∏ i ∈ Icc 1 n, partitionCount i

theorem partitionCount_pos (n : ℕ) : 0 < partitionCount n := by
  unfold partitionCount
  rw [Fintype.card_pos_iff]
  exact ⟨Nat.Partition.ofSums n {n} (by simp)⟩

theorem cumulativeProduct_pos (n : ℕ) :
    0 < cumulativePartitionProduct n := by
  unfold cumulativePartitionProduct
  exact Finset.prod_pos fun i _ => partitionCount_pos i

theorem cumulativeProduct_dvd_succ (n : ℕ) :
    cumulativePartitionProduct n ∣ cumulativePartitionProduct (n + 1) := by
  unfold cumulativePartitionProduct
  apply Finset.prod_dvd_prod_of_subset
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  omega

theorem proof : ∀ n : ℕ,
    (cumulativePartitionProduct n).primeFactors ⊆
      (cumulativePartitionProduct (n + 1)).primeFactors := by
  intro n
  exact Nat.primeFactors_mono (cumulativeProduct_dvd_succ n)
    (cumulativeProduct_pos (n + 1)).ne'

end Submissions.Erdos1106PrimeFactorMonotonicity.Direct

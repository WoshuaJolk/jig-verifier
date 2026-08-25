import Mathlib.Data.EReal.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENat
import Mathlib.Tactic

namespace Submissions.Erdos890WidthOneLiminf.Direct

open Filter Finset

def omegaGt (k n : ℕ) : ℕ :=
  (n.primeFactors.filter (· > k)).card

theorem power_two_count (e : ℕ) (he : 0 < e) :
    omegaGt 1 (2 ^ e) = 1 := by
  rw [omegaGt, Nat.primeFactors_prime_pow he.ne' Nat.prime_two]
  have hf : ({2} : Finset ℕ).filter (· > 1) = {2} := by
    ext x
    simp only [mem_filter, mem_singleton]
    omega
  rw [hf]
  simp

theorem proof :
    liminf
      (fun n : ℕ => (∑ i ∈ range 1, (omegaGt 1 (n + i) : EReal)))
      atTop ≤ 1 := by
  apply liminf_le_of_frequently_le'
  rw [frequently_atTop]
  intro N
  refine ⟨2 ^ (N + 1), ?_, ?_⟩
  · exact (Nat.le_of_lt N.lt_two_pow_self).trans
      (Nat.pow_le_pow_right (by decide) N.le_succ)
  · simp [power_two_count]

end Submissions.Erdos890WidthOneLiminf.Direct

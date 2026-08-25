import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos421InitialTermAtLeastTwo.Worker01

open Set

def DistinctBlocks (d : ℕ → ℕ) : Prop :=
  {(u, v) : ℕ × ℕ | u ≤ v}.InjOn
    (fun uv ↦ ∏ i ∈ Finset.Icc uv.1 uv.2, d i)

theorem proof :
    ∀ d : ℕ → ℕ, 1 ≤ d 0 → DistinctBlocks d → 2 ≤ d 0 := by
  intro d hpositive hinj
  by_contra hnot
  have hd0 : d 0 = 1 := by omega
  have h01 : (0, 1) ∈ {(u, v) : ℕ × ℕ | u ≤ v} := by simp
  have h11 : (1, 1) ∈ {(u, v) : ℕ × ℕ | u ≤ v} := by simp
  have heq : (∏ i ∈ Finset.Icc 0 1, d i) =
      ∏ i ∈ Finset.Icc 1 1, d i := by
    rw [Finset.prod_Icc_succ_top (by omega)]
    simp [hd0]
  have hpairs := hinj h01 h11 heq
  norm_num at hpairs

end Submissions.Erdos421InitialTermAtLeastTwo.Worker01

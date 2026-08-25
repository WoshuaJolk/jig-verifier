import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic

namespace Submissions.Erdos955ZeroFiber.Direct

def s (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

lemma s_eq_zero_iff (n : ℕ) : s n = 0 ↔ n ≤ 1 := by
  constructor
  · intro hs
    by_contra hn
    have hn' : 1 < n := by omega
    have hmem : 1 ∈ n.properDivisors :=
      Nat.one_mem_properDivisors_iff_one_lt.mpr hn'
    have hle : 1 ≤ s n := by
      unfold s
      exact Finset.single_le_sum (fun d _ => Nat.zero_le d) hmem
    omega
  · intro hn
    unfold s
    rw [Nat.properDivisors_eq_empty.mpr hn]
    simp

theorem proof : {n : ℕ | s n = 0} = Set.Iic 1 := by
  ext n
  exact s_eq_zero_iff n

end Submissions.Erdos955ZeroFiber.Direct

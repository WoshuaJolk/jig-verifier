import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace Submissions.Erdos410SigmaOrbitGrowth.Direct

open ArithmeticFunction

theorem sigma_strictly_grows (n : ℕ) (hn : 1 < n) :
    n < sigma 1 n := by
  have hn0 : n ≠ 0 := by omega
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with hd | hd
    · subst d
      exact Nat.one_mem_divisors.mpr hn0
    · subst d
      exact Nat.mem_divisors_self n hn0
  have hsum :
      (∑ d ∈ ({1, n} : Finset ℕ), d ^ 1) ≤
        ∑ d ∈ n.divisors, d ^ 1 :=
    Finset.sum_le_sum_of_subset hsub
  have hbound : 1 + n ≤ ∑ d ∈ n.divisors, d ^ 1 := by
    simpa only [Finset.sum_insert, Finset.sum_singleton, pow_one,
      Finset.mem_singleton, hn.ne, not_false_eq_true] using hsum
  rw [ArithmeticFunction.sigma_apply]
  omega

theorem proof : ∀ n > 1,
    StrictMono (fun k : ℕ => (sigma 1)^[k] n) ∧
      ∀ k : ℕ, n + k ≤ (sigma 1)^[k] n := by
  intro n hn
  have hlower : ∀ k : ℕ, n + k ≤ (sigma 1)^[k] n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have horbit : 1 < (sigma 1)^[k] n := lt_of_lt_of_le hn (by omega)
        have hgrowth := sigma_strictly_grows ((sigma 1)^[k] n) horbit
        omega
  refine ⟨strictMono_nat_of_lt_succ (fun k => ?_), hlower⟩
  rw [Function.iterate_succ_apply']
  have hnle : n ≤ (sigma 1)^[k] n := by
    exact le_trans (by omega) (hlower k)
  exact sigma_strictly_grows _ (hn.trans_le hnle)

end Submissions.Erdos410SigmaOrbitGrowth.Direct

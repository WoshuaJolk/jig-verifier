import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open scoped BigOperators

namespace Submissions.Erdos68FiniteRowTermination.FiniteRowTermination

private lemma denominator_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < n.factorial - 1 := by
  have hfac : 1 < n.factorial := Nat.one_lt_factorial.mpr (by omega)
  omega

private lemma denominator_dvd_common_factorial {n K : ℕ}
    (hn : 2 ≤ n) (hnK : n ≤ K) :
    n.factorial - 1 ∣ K.factorial.factorial := by
  apply Nat.dvd_factorial (denominator_pos hn)
  exact le_trans (Nat.sub_le _ _) (Nat.factorial_le hnK)

/-- Every single row has an explicit terminating factorial denominator, and all
rows through `K` share the computable factorial position `K!`. -/
theorem proof :
    (∀ n : ℕ, 2 ≤ n →
      let d := n.factorial - 1
      d ∣ d.factorial) ∧
    ∀ K : ℕ, 2 ≤ K →
      let Q := K.factorial.factorial
      let A :=
        ∑ n ∈ Finset.Icc 2 K, Q / (n.factorial - 1)
      (∑ n ∈ Finset.Icc 2 K,
          (1 : ℚ) / (n.factorial - 1 : ℕ)) =
        (A : ℚ) / Q := by
  constructor
  · intro n hn
    dsimp
    exact Nat.dvd_factorial (denominator_pos hn) le_rfl
  · intro K hK
    dsimp
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    have hnIcc := Finset.mem_Icc.mp hn
    have hdvd := denominator_dvd_common_factorial hnIcc.1 hnIcc.2
    have hd0 : ((n.factorial - 1 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (denominator_pos hnIcc.1))
    have hQ0 : ((K.factorial.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero K.factorial
    apply (div_eq_div_iff hd0 hQ0).2
    norm_num
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm

end Submissions.Erdos68FiniteRowTermination.FiniteRowTermination

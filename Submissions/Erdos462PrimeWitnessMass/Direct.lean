import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos462PrimeWitnessMass.Direct

open Finset

theorem proof :
    ∀ a b p : ℕ, p.Prime → p ∈ Icc a b →
      1 ≤ ∑ n ∈ Icc a b, (n.minFac : ℝ) / n := by
  intro a b p hp hpI
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  calc
    (1 : ℝ) = (p.minFac : ℝ) / p := by
      rw [Nat.Prime.minFac_eq hp]
      exact (div_self hp0).symm
    _ ≤ ∑ n ∈ Icc a b, (n.minFac : ℝ) / n := by
      apply Finset.single_le_sum
        (f := fun n : ℕ => (n.minFac : ℝ) / n)
      · intro n hn
        positivity
      · exact hpI

end Submissions.Erdos462PrimeWitnessMass.Direct

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

namespace Submissions.Erdos390ExtremalFactorUpperBound.Direct

open scoped Nat

noncomputable def extremalFactor (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k, ∃ a : ℕ → ℕ, StrictMono a ∧
    n < a 0 ∧ a (k - 1) = m ∧ ∏ i < k, a i = n !}

theorem proof : ∀ n : ℕ, 3 ≤ n → extremalFactor n ≤ n ! := by
  intro n hn
  apply Nat.sInf_le
  refine ⟨1, fun i => n ! + i, ?_, Nat.lt_factorial_self hn, by simp, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_left hij (n !)
  · have hIio : (Finset.Iio 1 : Finset ℕ) = {0} := by decide
    rw [hIio]
    simp

end Submissions.Erdos390ExtremalFactorUpperBound.Direct

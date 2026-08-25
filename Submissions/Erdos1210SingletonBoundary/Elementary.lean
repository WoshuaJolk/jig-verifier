import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

open Finset

namespace Submissions.Erdos1210SingletonBoundary.Elementary

theorem proof :
    ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a < n) →
      A.card ≤ 1 →
        ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤
          (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + 1 := by
  intro n A hrange hcard
  have hterm : ∀ a ∈ A, (1 / ((n : ℝ) - a)) ≤ (1 : ℝ) := by
    intro a ha
    have hden : (1 : ℝ) ≤ (n : ℝ) - a := by
      have hcast : (a : ℝ) + 1 ≤ n := by
        exact_mod_cast (Nat.add_one_le_iff.mpr (hrange a ha).2)
      linarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have hsum : (∑ a ∈ A, (1 / ((n : ℝ) - a))) ≤ (A.card : ℝ) := by
    simpa using A.sum_le_card_nsmul (fun a => (1 / ((n : ℝ) - a))) 1 hterm
  have hprime_nonneg : (0 : ℝ) ≤ ∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ)) := by
    positivity
  calc
    ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤ (A.card : ℝ) := hsum
    _ ≤ 1 := by exact_mod_cast hcard
    _ ≤ (∑ p ∈ (range n).filter Nat.Prime, (1 / (p : ℝ))) + 1 := by linarith

end Submissions.Erdos1210SingletonBoundary.Elementary

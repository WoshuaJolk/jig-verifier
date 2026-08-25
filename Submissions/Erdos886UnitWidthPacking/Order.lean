import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

open Nat

namespace Submissions.Erdos886UnitWidthPacking.Order

noncomputable def nearDivisors (n : ℕ) (ε C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1 / 2 : ℝ) < d ∧
      (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) +
        C * (n : ℝ) ^ (1 / 2 - ε))

theorem proof :
    ∀ n : ℕ, ∀ ε : ℝ,
      (n : ℝ) ^ (1 / 2 - ε) < 1 →
        (nearDivisors n ε 1).card ≤ 1 := by
  intro n ε hwidth
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [nearDivisors, Finset.mem_filter] at ha hb
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have hupper : (b : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + (n : ℝ) ^ (1 / 2 - ε) := by simpa using hb.2.2
    have hlower : (n : ℝ) ^ (1 / 2 : ℝ) < a := ha.2.1
    linarith
  · have hba' : (b : ℝ) + 1 ≤ a := by exact_mod_cast hba
    have hupper : (a : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + (n : ℝ) ^ (1 / 2 - ε) := by simpa using ha.2.2
    have hlower : (n : ℝ) ^ (1 / 2 : ℝ) < b := hb.2.1
    linarith

end Submissions.Erdos886UnitWidthPacking.Order

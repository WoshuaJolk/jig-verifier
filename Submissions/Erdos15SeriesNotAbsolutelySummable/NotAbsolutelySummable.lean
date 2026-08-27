import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
/-!
# Jig #253 (Erdős 15) is false as formalised: `Summable` is absolute convergence

Erdős problem 15 asks whether the **alternating** series `∑ (-1)^{n+1}(n+1)/pₙ`
converges — that is, whether its partial sums converge.  Mathlib's `Summable` is
unconditional summability, which for a real-valued series is equivalent to
absolute convergence (`summable_abs_iff`), a strictly stronger property.

The series is not absolutely convergent, and this needs none of the open problem:
`|term n| = (n+1)/pₙ ≥ 1/pₙ`, and `∑ 1/p` diverges over the primes
(`not_summable_one_div_on_primes`).  Transferring along the injection
`n ↦ pₙ`, whose range is exactly the primes, closes it.
-/

namespace Submissions.Erdos15SeriesNotAbsolutelySummable.NotAbsolutelySummable


noncomputable def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (n + 1) / Nat.nth Nat.Prime n

theorem refutation : ¬ Summable term := by
  intro h
  have hinf : {p | Nat.Prime p}.Infinite := Nat.infinite_setOfPred_prime
  have hprime : ∀ n : ℕ, (Nat.nth Nat.Prime n).Prime := Nat.prime_nth_prime
  have hpos : ∀ n : ℕ, (0:ℝ) < (Nat.nth Nat.Prime n : ℝ) := by
    intro n
    have := (hprime n).pos
    exact_mod_cast this
  -- absolute summability
  have habs : Summable (fun n => |term n|) := h.abs
  -- 1/p_n ≤ |term n|
  have hcomp : Summable (fun n : ℕ => 1 / (Nat.nth Nat.Prime n : ℝ)) := by
    refine habs.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have hp := hpos n
    rw [term, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ)+1)),
      abs_of_nonneg (le_of_lt hp)]
    rw [div_le_div_iff_of_pos_right hp]
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  -- transfer along the injection n ↦ p_n
  have hinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective (by simpa using hinf)
  have hrange : Set.range (Nat.nth Nat.Prime) = {p | Nat.Prime p} := by
    simpa using Nat.range_nth_of_infinite (p := Nat.Prime) (by simpa using hinf)
  have hzero : ∀ x ∉ Set.range (Nat.nth Nat.Prime),
      Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1:ℝ)/n) x = 0 := by
    intro x hx
    rw [hrange] at hx
    exact Set.indicator_of_notMem hx _
  have heq : (Set.indicator {p | Nat.Prime p} (fun m : ℕ => (1:ℝ)/m)) ∘ Nat.nth Nat.Prime
      = fun n : ℕ => 1 / (Nat.nth Nat.Prime n : ℝ) := by
    funext n
    exact Set.indicator_of_mem (hprime n) _
  have := (hinj.summable_iff hzero).1 (by rw [heq]; exact hcomp)
  exact not_summable_one_div_on_primes this


theorem proof : ¬ Summable term := refutation

end Submissions.Erdos15SeriesNotAbsolutelySummable.NotAbsolutelySummable

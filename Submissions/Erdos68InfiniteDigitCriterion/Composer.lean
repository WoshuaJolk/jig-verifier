import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68InfiniteDigitCriterion.Composer

noncomputable def factorialDigit (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋ -
    (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋

noncomputable def series : ℝ :=
  ∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)

private lemma scaled_integral (q : ℚ) {m : ℕ} (hm : q.den ≤ m) :
    ∃ z : ℤ, (m.factorial : ℝ) * (q : ℝ) = z := by
  have hdvd : q.den ∣ m.factorial :=
    Nat.dvd_factorial q.den_pos hm
  let k : ℕ := m.factorial / q.den
  let z : ℤ := q.num * k
  refine ⟨z, ?_⟩
  have hmul : k * q.den = m.factorial := by
    dsimp [k]
    exact Nat.div_mul_cancel hdvd
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast q.num_div_den.symm
  rw [hq]
  have hdenR : (q.den : ℝ) ≠ 0 := by
    exact_mod_cast q.den_ne_zero
  have hmulR : (m.factorial : ℝ) = (k : ℝ) * q.den := by
    exact_mod_cast hmul.symm
  dsimp [z]
  push_cast
  rw [hmulR]
  field_simp [hdenR]

private lemma rational_digit_zero (q : ℚ) {m : ℕ}
    (hm : q.den + 1 ≤ m) :
    factorialDigit (q : ℝ) m = 0 := by
  have hden : q.den ≤ m - 1 := by omega
  obtain ⟨z, hz⟩ := scaled_integral q hden
  have hfac : m.factorial = m * (m - 1).factorial :=
    (Nat.mul_factorial_pred (by omega : m ≠ 0)).symm
  have hscaled :
      (m.factorial : ℝ) * (q : ℝ) =
        (((m : ℤ) * z : ℤ) : ℝ) := by
    rw [hfac, Nat.cast_mul, mul_assoc, hz]
    norm_num
  have hprevFloor :
      ⌊((m - 1).factorial : ℝ) * (q : ℝ)⌋ = z := by
    rw [hz]
    exact Int.floor_intCast z
  have hcurrentFloor :
      ⌊(m.factorial : ℝ) * (q : ℝ)⌋ = (m : ℤ) * z := by
    rw [hscaled]
    exact Int.floor_intCast _
  simp [factorialDigit, hprevFloor, hcurrentFloor]

theorem proof :
    (∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ factorialDigit series m ≠ 0) →
      Irrational series := by
  intro hinfinite
  rw [Irrational]
  rintro ⟨q, hq⟩
  obtain ⟨m, hm, hnonzero⟩ := hinfinite (q.den + 1)
  apply hnonzero
  rw [← hq]
  exact rational_digit_zero q hm

end Submissions.Erdos68InfiniteDigitCriterion.Composer

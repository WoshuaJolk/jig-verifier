import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68RationalFactorialTermination.RationalFactorialTermination

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
  have hdenR : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hmulR :
      (m.factorial : ℝ) = (k : ℝ) * q.den := by
    exact_mod_cast hmul.symm
  dsimp [z]
  push_cast
  rw [hmulR]
  field_simp [hdenR]

/-- Every rational has an explicit terminating factorial expansion: its
denominator index suffices, all later canonical factorial digits vanish, and
the preceding factorial scale is integral. -/
theorem proof :
    ∀ q : ℚ,
      let N := q.den
      (∃ z : ℤ, (N.factorial : ℝ) * (q : ℝ) = z) ∧
      (∀ m : ℕ, N + 1 ≤ m →
        ⌊(m.factorial : ℝ) * (q : ℝ)⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * (q : ℝ)⌋ = 0) := by
  intro q
  dsimp
  constructor
  · exact scaled_integral q le_rfl
  · intro m hm
    have hden : q.den ≤ m - 1 := by omega
    obtain ⟨z, hz⟩ := scaled_integral q hden
    have hfac :
        m.factorial = m * (m - 1).factorial :=
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
    rw [hprevFloor, hcurrentFloor]
    omega

end Submissions.Erdos68RationalFactorialTermination.RationalFactorialTermination

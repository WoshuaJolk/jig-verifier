import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Submissions.Erdos68FactorialDigitFormula.FactorialDigitFormula

private lemma floor_stable_below_margin (y t : ℝ) (ht0 : 0 ≤ t)
    (ht : t < (⌊y⌋ : ℝ) + 1 - y) :
    ⌊y + t⌋ = ⌊y⌋ := by
  rw [Int.floor_eq_iff]
  constructor
  · exact (Int.floor_le y).trans (le_add_of_nonneg_right ht0)
  · linarith

/-- The canonical factorial digit lies in its radix range; a positive tail
preserves the relevant floor precisely when it is below the fractional margin;
and an already-integral preceding scale forces the digit to vanish. -/
theorem proof :
    (∀ m : ℕ, 1 ≤ m → ∀ x : ℝ,
      let a : ℤ :=
        ⌊(m.factorial : ℝ) * x⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋
      0 ≤ a ∧ a < m) ∧
    (∀ y t : ℝ, 0 ≤ t →
      t < (⌊y⌋ : ℝ) + 1 - y →
      ⌊y + t⌋ = ⌊y⌋) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, ∀ z : ℤ,
      ((m - 1).factorial : ℝ) * x = z →
      ⌊(m.factorial : ℝ) * x⌋ -
          (m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m hm x
    dsimp
    have hfac : m.factorial = m * (m - 1).factorial :=
      (Nat.mul_factorial_pred (by omega : m ≠ 0)).symm
    let y : ℝ := ((m - 1).factorial : ℝ) * x
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hlowerR :
        (m : ℝ) * (⌊y⌋ : ℝ) ≤ (m : ℝ) * y :=
      mul_le_mul_of_nonneg_left (Int.floor_le y) hm0
    have hlower :
        (m : ℤ) * ⌊y⌋ ≤ ⌊(m : ℝ) * y⌋ := by
      rw [Int.le_floor]
      exact_mod_cast hlowerR
    have hupperR :
        (m : ℝ) * y <
          ((m : ℤ) * (⌊y⌋ + 1) : ℤ) := by
      push_cast
      exact mul_lt_mul_of_pos_left (Int.lt_floor_add_one y)
        (by exact_mod_cast (by omega : 0 < m))
    have hupper :
        ⌊(m : ℝ) * y⌋ < (m : ℤ) * (⌊y⌋ + 1) := by
      rw [Int.floor_lt]
      exact hupperR
    have hscaled :
        (m.factorial : ℝ) * x = (m : ℝ) * y := by
      rw [hfac, Nat.cast_mul]
      dsimp [y]
      ring
    have hprev :
        ((m - 1).factorial : ℝ) * x = y := rfl
    rw [hscaled, hprev]
    rw [mul_add, mul_one] at hupper
    constructor <;> omega
  · exact floor_stable_below_margin
  · intro m hm x z hz
    have hfac : m.factorial = m * (m - 1).factorial :=
      (Nat.mul_factorial_pred (by omega : m ≠ 0)).symm
    have hscaled :
        (m.factorial : ℝ) * x = (((m : ℤ) * z : ℤ) : ℝ) := by
      rw [hfac, Nat.cast_mul, mul_assoc, hz]
      norm_num
    have hprevFloor :
        ⌊((m - 1).factorial : ℝ) * x⌋ = z := by
      rw [hz]
      exact Int.floor_intCast z
    rw [hscaled, hprevFloor, Int.floor_intCast]
    omega

end Submissions.Erdos68FactorialDigitFormula.FactorialDigitFormula

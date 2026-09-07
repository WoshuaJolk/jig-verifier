import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Submissions.Erdos30ScalarSmoothingObstruction.Savcab
/-- The scalar smoothing inequality alone permits a half-quarter-power excess,
for every positive smoothing scale, under the finite certificate product barrier.
This is a statement about the scalar relaxation, not about existence of Sidon sets. -/
theorem scalar_relaxation_all_scales_13_18
    (t k a b H : ℝ) (ht : 2 ≤ t)
    (hkl : t^2 ≤ k) (hku : k ≤ t^2 + t/2)
    (ha : 0 < a) (hb : 0 < b) (hH : 0 < H)
    (hab : (13:ℝ)/18 ≤ a*b) :
    k^2 ≤ (t^4 + b*H - 1) * (1 + a*(k-1)/H) := by
  have ht0 : 0 ≤ t := by linarith
  have ht2 : 4 ≤ t^2 := by nlinarith [sq_nonneg (t-2)]
  have ht4 : 16 ≤ t^4 := by nlinarith [sq_nonneg (t^2-4)]
  have hk0 : 0 ≤ k := by nlinarith
  have hk1 : 0 ≤ k-1 := by nlinarith
  have hu : (3:ℝ)/4*t^4 ≤ t^4-1 := by linarith
  have hv : (3:ℝ)/4*t^2 ≤ k-1 := by linarith
  have hbase : (9:ℝ)/16*t^6 ≤ (t^4-1)*(k-1) := by
    have h := mul_le_mul hu hv (by positivity : 0 ≤ (3:ℝ)/4*t^2)
      (by linarith : 0 ≤ t^4-1)
    nlinarith only [h]
  let X := b*H
  let Y := a*(t^4-1)*(k-1)/H
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact div_nonneg (mul_nonneg (mul_nonneg ha.le (by linarith)) hk1) hH.le
  have hXY : (13:ℝ)/32*t^6 ≤ X*Y := by
    calc
      (13:ℝ)/32*t^6 = ((13:ℝ)/18)*((9:ℝ)/16*t^6) := by ring
      _ ≤ (a*b)*((t^4-1)*(k-1)) :=
        mul_le_mul hab hbase (by positivity) (mul_nonneg ha.le hb.le)
      _ = X*Y := by
        dsimp [X, Y]
        field_simp [ne_of_gt hH] <;> ring
  have hsum : (5:ℝ)/4*t^3 ≤ X+Y := by
    by_contra hnot
    have hle : X+Y ≤ (5:ℝ)/4*t^3 := le_of_lt (lt_of_not_ge hnot)
    have hprod : 0 ≤ ((5:ℝ)/4*t^3-(X+Y))*((5:ℝ)/4*t^3+(X+Y)) :=
      mul_nonneg (sub_nonneg.mpr hle) (by positivity)
    have ht6 : 0 < t^6 := pow_pos (by linarith) 6
    nlinarith only [hprod, hXY, sq_nonneg (X-Y), ht6]
  have hkSquare : k^2 ≤ (t^2+t/2)^2 := by
    have hprod : 0 ≤ (t^2+t/2-k)*(t^2+t/2+k) :=
      mul_nonneg (sub_nonneg.mpr hku) (by positivity)
    nlinarith only [hprod]
  have hgapFactor : 0 ≤ (t-2)*(t^2+t+2) :=
    mul_nonneg (by linarith) (by positivity)
  have hgap : k^2-t^4+1 ≤ (5:ℝ)/4*t^3 := by
    nlinarith only [hkSquare, hgapFactor]
  have hextra : 0 ≤ a*b*(k-1) := mul_nonneg (mul_nonneg ha.le hb.le) hk1
  have heq : (t^4+b*H-1)*(1+a*(k-1)/H) =
      t^4-1+X+Y+a*b*(k-1) := by
    dsimp [X, Y]
    field_simp [ne_of_gt hH] <;> ring
  rw [heq]
  linarith

theorem proof : ∀ n : ℕ, 1 ≤ n → ∀ a b H : ℝ, 0 < a → 0 < b → 0 < H →
    (13:ℝ)/18 ≤ a*b →
    ((4*n^2+n : ℕ) : ℝ)^2 ≤
      (((16*n^4 : ℕ) : ℝ)+b*H-1) *
        (1+a*(((4*n^2+n : ℕ) : ℝ)-1)/H) := by
  intro n hn a b H ha hb hH hab
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hh := scalar_relaxation_all_scales_13_18
    (2*(n:ℝ)) (4*(n:ℝ)^2+n) a b H (by linarith)
    (by nlinarith) (by nlinarith) ha hb hH hab
  convert hh using 1 <;> push_cast <;> ring
end Submissions.Erdos30ScalarSmoothingObstruction.Savcab

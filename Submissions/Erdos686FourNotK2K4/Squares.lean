import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
`N = 4` is not a ratio of two consecutive products of length 2 or of length 4, for any `n, m`.

Both lengths reduce to `X² + 3 = Y²` with `X ≥ 3`:
* `k = 2`: `4(n+1)(n+2) = (2n+3)² − 1`, so `(m+1)(m+2) = 4(n+1)(n+2)` gives
  `(2m+3)² + 3 = (4n+6)²`.
* `k = 4`: `(x+1)(x+2)(x+3)(x+4) = (x²+5x+5)² − 1`, so the equation gives
  `(m²+5m+5)² + 3 = (2(n²+5n+5))²`.
And `X² + 3 = Y²` with `X ≥ 3` is impossible: `Y > X` forces `Y² ≥ X² + 2X + 1 ≥ X² + 7`.
-/

namespace Submissions.Erdos686FourNotK2K4.Squares

open scoped BigOperators

/-- `X² + 3 = Y²` has no solution with `X ≥ 3`. -/
lemma no_sq_plus_three (X Y : ℕ) (hX : 3 ≤ X) (h : X ^ 2 + 3 = Y ^ 2) : False := by
  have hlt : X < Y := by nlinarith
  have hle : X + 1 ≤ Y := hlt
  nlinarith

lemma k2 (n m : ℕ) (h : 4 * ((n + 1) * (n + 2)) = (m + 1) * (m + 2)) : False :=
  no_sq_plus_three (2 * m + 3) (4 * n + 6) (by omega) (by nlinarith)

lemma k4 (n m : ℕ)
    (h : 4 * ((n + 1) * (n + 2) * (n + 3) * (n + 4)) = (m + 1) * (m + 2) * (m + 3) * (m + 4)) :
    False :=
  no_sq_plus_three (m ^ 2 + 5 * m + 5) (2 * (n ^ 2 + 5 * n + 5)) (by nlinarith) (by nlinarith)

theorem proof : ∀ n m : ℕ,
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 2, (m + i)) / (∏ i ∈ Finset.Icc 1 2, (n + i)) ∧
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 4, (m + i)) / (∏ i ∈ Finset.Icc 1 4, (n + i)) := by
  intro n m
  constructor
  · intro h
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num), Finset.prod_pair (by norm_num)] at h
    rw [eq_div_iff (by positivity)] at h
    norm_cast at h
    exact k2 n m h
  · intro h
    rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide] at h
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)] at h
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)] at h
    rw [eq_div_iff (by positivity)] at h
    norm_cast at h
    exact k4 n m (by linarith [h])

end Submissions.Erdos686FourNotK2K4.Squares

import Mathlib

/- BEGIN bundled local module ProductColorLaw -/


namespace ColeskiProductColorLaw
open Finset
variable {E C : Type*} [Fintype E] [Fintype C] [DecidableEq E]

def mass (w : E → C → ℝ) (a : E → C) : ℝ := ∏ e, w e (a e)

theorem nonnegative (w : E → C → ℝ) (h : ∀ e c, 0 ≤ w e c) (a : E → C) :
    0 ≤ mass w a := Finset.prod_nonneg (fun e _ => h e (a e))

theorem normalized (w : E → C → ℝ) (h : ∀ e, ∑ c, w e c = 1) :
    ∑ a : E → C, mass w a = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp [h]

theorem zero_of_zero_factor (w : E → C → ℝ) (a : E → C) (e : E)
    (h : w e (a e) = 0) : mass w a = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ e) h

theorem positive_factors (w : E → C → ℝ) (h : ∀ e c, 0 ≤ w e c)
    (a : E → C) (ha : 0 < mass w a) (e : E) : 0 < w e (a e) := by
  apply lt_of_le_of_ne (h e (a e))
  intro hz
  have hm := zero_of_zero_factor w a e hz.symm
  rw [hm] at ha
  exact (lt_irrefl 0) ha

end ColeskiProductColorLaw
#print axioms ColeskiProductColorLaw.normalized
#print axioms ColeskiProductColorLaw.positive_factors

/- END bundled local module ProductColorLaw -/

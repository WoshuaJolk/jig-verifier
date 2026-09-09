import Commons.ColeskiE811Sig20260909_ProductColorLaw

/- BEGIN bundled local module IndependentColorMoment -/


namespace ColeskiIndependentColorMoment
open Finset
variable {E C : Type*} [Fintype E] [Fintype C] [DecidableEq E]

theorem single_coordinate (w : E → C → ℝ) (hn : ∀ e, ∑ c, w e c = 1)
    (m : E) (f : C → ℝ) :
    (∑ a : E → C, ColeskiProductColorLaw.mass w a * f (a m)) = ∑ c, w m c * f c := by
  classical
  let g : E → C → ℝ := fun e c => w e c * (if e = m then f c else 1)
  have hg (a : E → C) : (∏ e, g e (a e)) = ColeskiProductColorLaw.mass w a * f (a m) := by
    dsimp only [g]
    rw [Finset.prod_mul_distrib]
    simp [ColeskiProductColorLaw.mass]
  rw [← show (∑ a, ∏ e, g e (a e)) = ∑ a, ColeskiProductColorLaw.mass w a * f (a m) from
    Finset.sum_congr rfl (fun a _ => hg a), ← Fintype.prod_sum]
  rw [Finset.prod_eq_single m]
  · simp [g]
  · intro e _ he
    simp [g,he,hn]
  · simp

theorem centered (w : E → Fin 6 → ℝ) (hn : ∀ e, ∑ c, w e c = 1)
    (m : E) (c : Fin 6) :
    (∑ a : E → Fin 6, ColeskiProductColorLaw.mass w a *
      ((if a m = c then (6 : ℝ) else 0) - 1)) = 6 * w m c - 1 := by
  classical
  rw [single_coordinate w hn m (fun d => (if d = c then (6 : ℝ) else 0) - 1)]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [mul_ite,hn,mul_comm]

end ColeskiIndependentColorMoment
#print axioms ColeskiIndependentColorMoment.single_coordinate
#print axioms ColeskiIndependentColorMoment.centered

/- END bundled local module IndependentColorMoment -/

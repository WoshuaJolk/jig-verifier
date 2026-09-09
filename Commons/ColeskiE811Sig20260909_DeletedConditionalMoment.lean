import Commons.ColeskiE811Sig20260909_DeletedAssignmentSplit
import Commons.ColeskiE811Sig20260909_IndependentColorMoment

/- BEGIN bundled local module DeletedConditionalMoment -/


namespace ColeskiDeletedConditionalMoment
open ColeskiSixVertexLaw ColeskiDeletedEdgeSplit ColeskiDeletedAssignmentSplit

theorem sum_incident (z : Fin 6) (w : Edge → Fin 6 → ℝ)
    (hn : ∀ e, ∑ c, w e c = 1) (H : (BaseEdge → Fin 6) → ℝ)
    (m : Fin 5) (c : Fin 6) :
    (∑ a : Edge → Fin 6, ColeskiProductColorLaw.mass w a * H (assignments z a).1 *
      ((if (assignments z a).2 m = c then (6 : ℝ) else 0) - 1)) =
    (∑ b : BaseEdge → Fin 6, ColeskiProductColorLaw.mass (fun e => w (base z e)) b * H b) *
      (6 * w (star z m) c - 1) := by
  classical
  rw [← Equiv.sum_comp (assignments z).symm
    (fun a => ColeskiProductColorLaw.mass w a * H (assignments z a).1 *
      ((if (assignments z a).2 m = c then (6 : ℝ) else 0) - 1))]
  simp_rw [probability_split z,Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [← ColeskiIndependentColorMoment.centered (fun m => w (star z m))
    (fun m => hn (star z m)) m c,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end ColeskiDeletedConditionalMoment
#print axioms ColeskiDeletedConditionalMoment.sum_incident

/- END bundled local module DeletedConditionalMoment -/

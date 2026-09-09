import Commons.ColeskiE811Sig20260909_DeletedEdgeSplit

/- BEGIN bundled local module DeletedAssignmentSplit -/


namespace ColeskiDeletedAssignmentSplit
open ColeskiSixVertexLaw ColeskiDeletedEdgeSplit

noncomputable def assignments (z : Fin 6) :
    (Edge → Fin 6) ≃ (BaseEdge → Fin 6) × (Fin 5 → Fin 6) :=
  (Equiv.arrowCongr (edgeEquiv z).symm (Equiv.refl (Fin 6))).trans
    (Equiv.sumArrowEquivProdArrow BaseEdge (Fin 5) (Fin 6))

theorem base_assignment (z : Fin 6) (a : Edge → Fin 6) (e : BaseEdge) :
    (assignments z a).1 e = a (base z e) := rfl

theorem star_assignment (z : Fin 6) (a : Edge → Fin 6) (m : Fin 5) :
    (assignments z a).2 m = a (star z m) := rfl

theorem probability_split (z : Fin 6) (w : Edge → Fin 6 → ℝ) (a : Edge → Fin 6) :
    ColeskiProductColorLaw.mass w a =
      ColeskiProductColorLaw.mass (fun e => w (base z e)) (assignments z a).1 *
      ColeskiProductColorLaw.mass (fun m => w (star z m)) (assignments z a).2 := by
  unfold ColeskiProductColorLaw.mass
  rw [← Equiv.prod_comp (edgeEquiv z) (fun e => w e (a e))]
  rw [Fintype.prod_sum_type]
  rfl

end ColeskiDeletedAssignmentSplit
#print axioms ColeskiDeletedAssignmentSplit.probability_split

/- END bundled local module DeletedAssignmentSplit -/

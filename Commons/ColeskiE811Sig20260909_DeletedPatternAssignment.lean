import Commons.ColeskiE811Sig20260909_DeletedAssignmentSplit
import Commons.ColeskiE811Sig20260909_DeletionAction

/- BEGIN bundled local module DeletedPatternAssignment -/


namespace ColeskiDeletedPatternAssignment
open ColeskiSixVertexLaw ColeskiSixEdgePattern ColeskiDeletedEdgeSplit
open ColeskiDeletedAssignmentSplit ColeskiPatternAction ColeskiDeletionAction

def basePattern (b : BaseEdge → Fin 6) : Pattern (Fin 5) (Fin 6) := fun u v =>
  if h : u < v then some (b ⟨(u,v),h⟩)
  else if h : v < u then some (b ⟨(v,u),h⟩) else none

theorem deleted_pattern (z : Fin 6) (a : Edge → Fin 6) :
    deletePattern (pattern a) z = basePattern (assignments z a).1 := by
  funext u v
  have hinj := (Fin.succAboveOrderEmb z).injective
  by_cases he : u = v
  · subst v
    simp [deletePattern,pattern,ColeskiColoringPattern.coloredPattern,basePattern]
  · have hne : z.succAbove u ≠ z.succAbove v := hinj.ne he
    by_cases h : u < v
    · have hh := (Fin.succAboveOrderEmb z).strictMono h
      simp [deletePattern,pattern,ColeskiColoringPattern.coloredPattern,basePattern,
        color,h,hh,hne,base_assignment,base]
    · have hv : v < u := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm he)
      have hh := (Fin.succAboveOrderEmb z).strictMono hv
      have hn := not_lt_of_ge (le_of_lt hh)
      simp [deletePattern,pattern,ColeskiColoringPattern.coloredPattern,basePattern,
        color,h,hv,hh,hn,hne,base_assignment,base]

theorem marked_color (z : Fin 6) (a : Edge → Fin 6) (m : Fin 5) :
    ((pattern a) (z.succAbove m) z).getD 0 = (assignments z a).2 m := by
  rw [star_assignment]
  simp only [pattern,ColeskiColoringPattern.coloredPattern,Fin.succAbove_ne,
    if_false,Option.getD_some]
  by_cases h : z < z.succAbove m
  · have hn := not_lt_of_ge (le_of_lt h)
    simp [color,ColeskiDeletedEdgeSplit.star,h,hn,
      min_eq_left (le_of_lt h),max_eq_right (le_of_lt h)]
  · have hh : z.succAbove m < z :=
      lt_of_le_of_ne (le_of_not_gt h) (Fin.succAbove_ne z m)
    simp [color,ColeskiDeletedEdgeSplit.star,hh,
      min_eq_right (le_of_lt hh),max_eq_left (le_of_lt hh)]

end ColeskiDeletedPatternAssignment
#print axioms ColeskiDeletedPatternAssignment.deleted_pattern
#print axioms ColeskiDeletedPatternAssignment.marked_color

/- END bundled local module DeletedPatternAssignment -/

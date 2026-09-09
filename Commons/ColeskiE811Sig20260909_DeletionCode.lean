import Commons.ColeskiE811Sig20260909_SixExtension
import Commons.ColeskiE811Sig20260909_DeletionAction
import Commons.ColeskiE811Sig20260909_EdgeIndexTable

/- BEGIN bundled local module DeletionCode -/

namespace ColeskiDeletionCode
open ColeskiPatternAction ColeskiPatternCode ColeskiK4Coverage ColeskiK5Coverage
open ColeskiK6Check ColeskiK6RealCertificate ColeskiSixExtension ColeskiDeletionAction
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem skip_value (z : Fin 6) (i : Fin 5) : (z.succAbove i).val = skip z.val i.val := by
  fin_cases z <;> fin_cases i <;> decide

def deletionEdge (r a z : Nat) (e : Fin 10) : Fin 6 :=
  colorFin r a (skip z (edgeLeft5 e.val)) (skip z (edgeRight5 e.val))

theorem deletionCode_encode (r a z : Nat) : deletionCode r a z = encode10 (deletionEdge r a z) := by
  change 0 + 1*(deletionEdge r a z 0).val + 6*(deletionEdge r a z 1).val + 36*(deletionEdge r a z 2).val + 216*(deletionEdge r a z 3).val + 1296*(deletionEdge r a z 4).val + 7776*(deletionEdge r a z 5).val + 46656*(deletionEdge r a z 6).val + 279936*(deletionEdge r a z 7).val + 1679616*(deletionEdge r a z 8).val + 10077696*(deletionEdge r a z 9).val = (deletionEdge r a z 0).val + 6*(deletionEdge r a z 1).val + 36*(deletionEdge r a z 2).val + 216*(deletionEdge r a z 3).val + 1296*(deletionEdge r a z 4).val + 7776*(deletionEdge r a z 5).val + 46656*(deletionEdge r a z 6).val + 279936*(deletionEdge r a z 7).val + 1679616*(deletionEdge r a z 8).val + 10077696*(deletionEdge r a z 9).val
  simp only [Nat.one_mul,Nat.zero_add]

theorem edge_distinct (e : Fin 10) : (edgeVertices e).1 ≠ (edgeVertices e).2 := by
  fin_cases e <;> decide

theorem delete_edge (r a : Nat) (z : Fin 6) (e : Fin 10) :
    ((deletePattern (sixPattern r a) z) (edgeVertices e).1 (edgeVertices e).2).getD 0 =
      deletionEdge r a z.val e := by
  have hn : z.succAbove (edgeVertices e).1 ≠ z.succAbove (edgeVertices e).2 :=
    (Fin.succAboveEmb z).injective.ne (edge_distinct e)
  simp only [deletePattern,sixPattern,if_neg hn,Option.getD_some]
  apply Fin.ext
  change edgeColor r a (z.succAbove (edgeVertices e).1).val
    (z.succAbove (edgeVertices e).2).val = _
  rw [skip_value,skip_value,(ColeskiPatternTransform.edge_vertices_code e).1,
    (ColeskiPatternTransform.edge_vertices_code e).2]
  rfl

theorem patternCode_delete (r a : Nat) (z : Fin 6) :
    patternCode (deletePattern (sixPattern r a) z) = deletionCode r a z.val := by
  rw [deletionCode_encode]
  simp only [patternCode,delete_edge]

theorem sixPattern_symmetric (r a : Nat) : ∀ u v, sixPattern r a u v = sixPattern r a v u := by
  intro u v
  simp [sixPattern,colorFin,edgeColor,eq_comm,Nat.min_comm,Nat.max_comm]

theorem sixPattern_no_loops (r a : Nat) : ∀ u, sixPattern r a u u = none := by
  intro u
  simp [sixPattern]

theorem sixPattern_full (r a : Nat) : ∀ u v, u ≠ v → sixPattern r a u v ≠ none := by
  intro u v h
  simp [sixPattern,h]

theorem deletePattern_eq_fromCode (r a : Nat) (z : Fin 6) :
    deletePattern (sixPattern r a) z = fromCode (deletionCode r a z.val) := by
  have hr := reconstruct (deletePattern (sixPattern r a) z)
    (fun u v => sixPattern_symmetric r a _ _)
    (fun u => sixPattern_no_loops r a _)
    (fun u v h => sixPattern_full r a _ _ ((Fin.succAboveEmb z).injective.ne h))
  rw [patternCode_delete] at hr
  exact hr.symm

theorem incident_color (r a : Nat) (z : Fin 6) (m : Fin 5) :
    ((sixPattern r a) (z.succAbove m) z).getD 0 = colorFin r a (skip z.val m.val) z.val := by
  simp only [sixPattern,if_neg (Fin.succAbove_ne z m),Option.getD_some]
  rw [skip_value]
end ColeskiDeletionCode
#print axioms ColeskiDeletionCode.deletePattern_eq_fromCode
#print axioms ColeskiDeletionCode.incident_color

/- END bundled local module DeletionCode -/

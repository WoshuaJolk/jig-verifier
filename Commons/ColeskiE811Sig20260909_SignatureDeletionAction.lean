import Commons.ColeskiE811Sig20260909_DeletionPermutation
import Commons.ColeskiE811Sig20260909_PatternValidity
import Commons.ColeskiE811Sig20260909_SignatureWeights

/- BEGIN bundled local module SignatureDeletionAction -/


namespace ColeskiSignatureDeletionAction

open ColeskiDeletionPermutation ColeskiPatternAction ColeskiPaletteAction
open ColeskiPatternValidity ColeskiFlagSignature ColeskiSignatureWeights

def deletePattern (x : Pattern (Fin 6) (Fin 6)) (z : Fin 6) : FivePattern :=
  fun u v => x (z.succAbove u) (z.succAbove v)

noncomputable def deleteAction (g : Symmetry (V := Fin 6) colorGroup) (z : Fin 6) : G :=
  (deletionPerm g.1 z, g.2)

theorem delete_valid (x : Pattern (Fin 6) (Fin 6)) (h : Valid x) (z : Fin 6) :
    Valid (deletePattern x z) := valid_restrict (Fin.succAboveEmb z) x h

theorem deletion_transport (g : Symmetry (V := Fin 6) colorGroup)
    (x : Pattern (Fin 6) (Fin 6)) (z : Fin 6) :
    deletePattern (g • x) (g.1 z) = deleteAction g z • deletePattern x z := by
  funext u v
  change (x (g.1⁻¹ ((g.1 z).succAbove u)) (g.1⁻¹ ((g.1 z).succAbove v))).map g.2.val =
    (x (z.succAbove ((deletionPerm g.1 z)⁻¹ u))
      (z.succAbove ((deletionPerm g.1 z)⁻¹ v))).map g.2.val
  rw [embed_inverse, embed_inverse]

theorem deletion_coefficient_transport
    (g : Symmetry (V := Fin 6) colorGroup) (x : Pattern (Fin 6) (Fin 6))
    (z : Fin 6) (m : Fin 5) (c : Fin 6) :
    coefficientFor (deletePattern (g • x) (g.1 z))
        (deletionPerm g.1 z m, g.2.val c) =
      coefficientFor (deletePattern x z) (m, c) := by
  rw [deletion_transport]
  exact coefficientFor_transport (deleteAction g z) (deletePattern x z) (m, c)

theorem edge_transport (g : Symmetry (V := Fin 6) colorGroup)
    (x : Pattern (Fin 6) (Fin 6)) (h : Valid x) (z : Fin 6) (m : Fin 5) :
    ((g • x) ((g.1 z).succAbove (deletionPerm g.1 z m)) (g.1 z)).getD 0 =
      g.2.val ((x (z.succAbove m) z).getD 0) := by
  rw [embed_permute]
  change ((x (g.1⁻¹ (g.1 (z.succAbove m))) (g.1⁻¹ (g.1 z))).map g.2.val).getD 0 = _
  simpa using getD_map g.2.val (x (z.succAbove m) z)
    (h.2.2.1 _ _ (Fin.succAbove_ne z m))

end ColeskiSignatureDeletionAction

#print axioms ColeskiSignatureDeletionAction.deletion_coefficient_transport

/- END bundled local module SignatureDeletionAction -/

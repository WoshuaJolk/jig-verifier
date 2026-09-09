import Statements.E811DesignPalette
import Commons.ColeskiE811Sig20260909_GraphonConditionalBalance
import Commons.ColeskiE811Sig20260909_GraphonPaletteSupport
import Commons.ColeskiE811Sig20260909_DeletedPatternAssignment
import Commons.ColeskiE811Sig20260909_PatternLawObstruction
import Commons.ColeskiE811Sig20260909_SignaturePatternLawObstruction

/- BEGIN bundled local module SignatureDesignPaletteReduction -/


namespace ColeskiSignatureDesignPaletteReduction

open MeasureTheory ColeskiSixVertexLaw ColeskiSixEdgePattern ColeskiDeletedPatternAssignment
open ColeskiDeletedAssignmentSplit ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
open ColeskiSignatureRows ColeskiFlagSignature ColeskiSignatureDeletionAction

theorem palette_eq :
    Statements.E811DesignPalette.designTriples = ColeskiK4Coverage.palettes := by decide

theorem deleted_pattern (z : Fin 6) (a : Edge → Fin 6) :
    deletePattern (pattern a) z = basePattern (assignments z a).1 := by
  exact ColeskiDeletedPatternAssignment.deleted_pattern z a

theorem target_from_checks
    (rows : ∀ r : Fin 551, rowMatches r)
    (positive : ∀ r : Fin 551, ∀ a : Fin 7776,
      allowedExtension6 representatives5[r.val]! a.val = true →
      ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true) :
    Statements.E811DesignPalette.statement := by
  classical
  intro Ω _ μ hμ W hm hb hs ht hd hz
  letI := hμ
  apply False.elim
  apply ColeskiSignaturePatternLawObstruction.impossible rows positive (mass μ W) pattern
    (mass_nonnegative μ W hb) (mass_normalized μ W hm hb ht)
  · apply ColeskiGraphonPaletteSupport.supported μ W hm hb hs
    intro i j k hij hjk hik hpal
    apply hz i j k hij hjk (Ne.symm hik)
    rwa [palette_eq]
  · intro z m c p
    let H : (ColeskiDeletedEdgeSplit.BaseEdge → Fin 6) → ℝ :=
      fun b => if basePattern b = p then 1 else 0
    have hh := ColeskiGraphonConditionalBalance.balanced μ W hm hb hs ht hd z m c H
    calc
      _ = ∑ a : Edge → Fin 6, mass μ W a * (H (assignments z a).1 *
        ((if (assignments z a).2 m = c then (6 : ℝ) else 0) - 1)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [deleted_pattern, ColeskiDeletedPatternAssignment.marked_color]
          by_cases h : basePattern (assignments z a).1 = p
          · simp [H, h]
          · simp [H, h]
      _ = 0 := hh

end ColeskiSignatureDesignPaletteReduction

#print axioms ColeskiSignatureDesignPaletteReduction.target_from_checks

/- END bundled local module SignatureDesignPaletteReduction -/

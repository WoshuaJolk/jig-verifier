import Commons.ColeskiE811Sig20260909_PaletteAction
import Commons.ColeskiE811Sig20260909_PatternFaithfulness

/- BEGIN bundled local module WitnessAction -/

namespace ColeskiWitnessAction
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar
open ColeskiPaletteAction ColeskiPatternFaithfulness ColeskiPatternAction

def repIndex (w : Fin 3967200) : Fin 551 := ⟨w.val/7200, by omega⟩
def vertexIndex (w : Fin 3967200) : Fin 120 := ⟨w.val/60%120, Nat.mod_lt _ (by decide)⟩
def colorIndex (w : Fin 3967200) : Fin 60 := ⟨w.val%60, Nat.mod_lt _ (by decide)⟩
noncomputable def witnessAction (w : Fin 3967200) : G := tableAction (vertexIndex w) (colorIndex w)

theorem packed (w : Fin 3967200) :
    1+(colorIndex w).val+60*(vertexIndex w).val+7200*(repIndex w).val = w.val+1 := by
  dsimp [colorIndex,vertexIndex,repIndex]
  omega

theorem witnessAction_pattern (w : Fin 3967200) :
    witnessAction w • fromCode representatives5[(repIndex w).val]! =
      fromCode (transformed5 (w.val+1)) := by
  have h := reconstruct_transport colorGroup (witnessAction w) representatives5[(repIndex w).val]!
  change fromCode (patternCode (witnessAction w • fromCode representatives5[(repIndex w).val]!)) =
    witnessAction w • fromCode representatives5[(repIndex w).val]! at h
  unfold witnessAction at h
  rw [tableAction_code, ← transformed_components (repIndex w) (vertexIndex w) (colorIndex w), packed] at h
  exact h.symm

theorem witnessAction_eq (w : Fin 3967200) (n : Nat)
    (h : transformed5 (w.val+1) = n) :
    witnessAction w • fromCode representatives5[(repIndex w).val]! = fromCode n := by
  rw [witnessAction_pattern,h]
end ColeskiWitnessAction
#print axioms ColeskiWitnessAction.witnessAction_pattern

/- END bundled local module WitnessAction -/

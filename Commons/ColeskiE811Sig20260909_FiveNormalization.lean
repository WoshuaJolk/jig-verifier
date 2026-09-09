import Commons.ColeskiE811Sig20260909_FourNormalization
import Commons.ColeskiE811Sig20260909_FiveAllowed
import Commons.ColeskiE811Sig20260909_LiftAction
import Commons.ColeskiE811Sig20260909_WitnessAction

/- BEGIN bundled local module FiveNormalization -/

namespace ColeskiFiveNormalization
open ColeskiPatternAction ColeskiPatternCode ColeskiK4Coverage ColeskiK5Coverage
open ColeskiPatternValidity ColeskiFourPermutation ColeskiLiftAction ColeskiPaletteAction
open ColeskiFiveExtension ColeskiFiveAllowed ColeskiArmCode ColeskiCoverageWitnesses ColeskiWitnessAction
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem normalize (x : Pattern (Fin 5) (Fin 6)) (h : Valid x) :
    ∃ i : Fin 551, ∃ g : G, g • fromCode representatives5[i.val]! = x := by
  let x4 : Pattern (Fin 4) (Fin 6) := fun u v => x u.castSucc v.castSucc
  have h4valid : Valid x4 := valid_restrict (initialEmbedding 4) x h
  obtain ⟨r,g4,h4⟩ := ColeskiFourNormalization.normalize x4 h4valid.1 h4valid.2.1
    h4valid.2.2.1 h4valid.2.2.2
  change g4 • ColeskiPatternFour.fromCode representatives[r.val]! =
    (fun u v : Fin 4 => x u.castSucc v.castSucc) at h4
  let g5 : G := liftSymmetry g4⁻¹
  let y : Pattern (Fin 5) (Fin 6) := g5 • x
  have hyvalid : Valid y := valid_transport g5 x h
  have hybase : (fun u v : Fin 4 => y u.castSucc v.castSucc) =
      ColeskiPatternFour.fromCode representatives[r.val]! := by
    change (fun u v : Fin 4 => (liftSymmetry g4⁻¹ • x) u.castSucc v.castSucc) = _
    rw [restrict_lift,← h4,inv_smul_smul]
  have hb (u v : Fin 4) : y u.castSucc v.castSucc =
      ColeskiPatternFour.fromCode representatives[r.val]! u v := congrFun (congrFun hybase u) v
  let a : Fin 1296 := ⟨encodeArm (arms y),encodeArm_lt _⟩
  have ha : allowedExtension representatives[r.val]! a.val = true := normalized_allowed y _ hyvalid hb
  obtain ⟨w,hw⟩ := witness5_exists r a ha
  have hwy := witnessAction_eq w (extendCode representatives[r.val]! a.val) hw
  have hyr : fromCode (extendCode representatives[r.val]! a.val) = y :=
    reconstruct_extended y _ hyvalid.1 hyvalid.2.1 hyvalid.2.2.1 hb
  have hy : witnessAction w • fromCode representatives5[(repIndex w).val]! = y := hwy.trans hyr
  refine ⟨repIndex w,g5⁻¹*witnessAction w,?_⟩
  rw [mul_smul,hy]
  exact inv_smul_smul g5 x
end ColeskiFiveNormalization
#print axioms ColeskiFiveNormalization.normalize

/- END bundled local module FiveNormalization -/

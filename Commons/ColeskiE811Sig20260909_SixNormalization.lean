import Commons.ColeskiE811Sig20260909_FiveNormalization
import Commons.ColeskiE811Sig20260909_SixAllowed
import Commons.ColeskiE811Sig20260909_SixExtension

/- BEGIN bundled local module SixNormalization -/

namespace ColeskiSixNormalization
open ColeskiPatternAction ColeskiPatternCode ColeskiK5Coverage ColeskiPatternValidity
open ColeskiFourPermutation ColeskiLiftAction ColeskiPaletteAction ColeskiSixExtension ColeskiSixAllowed ColeskiArmFive
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem normalize (x : Pattern (Fin 6) (Fin 6)) (h : Valid x) :
    ∃ r : Fin 551, ∃ a : Fin 7776, ∃ g : Symmetry (V := Fin 6) colorGroup,
      allowedExtension6 representatives5[r.val]! a.val = true ∧
      g • sixPattern representatives5[r.val]! a.val = x := by
  let x5 : Pattern (Fin 5) (Fin 6) := fun u v => x u.castSucc v.castSucc
  have h5valid : Valid x5 := valid_restrict (initialEmbedding 5) x h
  obtain ⟨r,g5,h5⟩ := ColeskiFiveNormalization.normalize x5 h5valid
  change g5 • fromCode representatives5[r.val]! =
    (fun u v : Fin 5 => x u.castSucc v.castSucc) at h5
  let g6 : Symmetry (V := Fin 6) colorGroup := liftSymmetry g5⁻¹
  let y : Pattern (Fin 6) (Fin 6) := g6 • x
  have hyvalid : Valid y := valid_transport g6 x h
  have hybase : (fun u v : Fin 5 => y u.castSucc v.castSucc) = fromCode representatives5[r.val]! := by
    change (fun u v : Fin 5 => (liftSymmetry g5⁻¹ • x) u.castSucc v.castSucc) = _
    rw [restrict_lift,← h5,inv_smul_smul]
  have hb (u v : Fin 5) : y u.castSucc v.castSucc = fromCode representatives5[r.val]! u v :=
    congrFun (congrFun hybase u) v
  let a : Fin 7776 := ⟨encodeArm (arms y),encodeArm_lt _⟩
  have ha : allowedExtension6 representatives5[r.val]! a.val = true := normalized_allowed y _ hyvalid hb
  have hr : sixPattern representatives5[r.val]! a.val = y :=
    reconstruct_extended y _ hyvalid.1 hyvalid.2.1 hyvalid.2.2.1 hb
  refine ⟨r,a,g6⁻¹,ha,?_⟩
  rw [hr]
  exact inv_smul_smul g6 x
end ColeskiSixNormalization
#print axioms ColeskiSixNormalization.normalize

/- END bundled local module SixNormalization -/

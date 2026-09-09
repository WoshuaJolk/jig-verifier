import Commons.ColeskiE811Sig20260909_PatternFourTransform
import Commons.ColeskiE811Sig20260909_CoverageWitnesses

/- BEGIN bundled local module FourNormalization -/

namespace ColeskiFourNormalization
open ColeskiK4Coverage ColeskiPatternFour ColeskiPatternFourTransform
open ColeskiPaletteAction ColeskiPatternAction ColeskiPatternFaithfulness ColeskiCoverageWitnesses
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem normalize (x : Pattern (Fin 4) (Fin 6))
    (hs : ∀ u v, x u v = x v u) (hd : ∀ u, x u u = none)
    (hf : ∀ u v, u ≠ v → x u v ≠ none)
    (ha : ∀ u v w, u ≠ v → u ≠ w → v ≠ w →
      good ((x u v).getD 0) ((x u w).getD 0) ((x v w).getD 0) = true) :
    ∃ r : Fin 25, ∃ g : Symmetry (V := Fin 4) colorGroup,
      g • fromCode representatives[r.val]! = x := by
  let k : Fin 46656 := ⟨patternCode x,encode_lt _⟩
  have hk : allowed k.val = true := code_allowed x ha
  obtain ⟨w,hw⟩ := witness4_exists k hk
  let r : Fin 25 := ⟨w.val/1440,by omega⟩
  let v : Fin 24 := ⟨w.val/60%24,Nat.mod_lt _ (by decide)⟩
  let c : Fin 60 := ⟨w.val%60,Nat.mod_lt _ (by decide)⟩
  let g := tableAction4 v c
  have hp : 1+c.val+60*v.val+1440*r.val = w.val+1 := by
    dsimp [r,v,c]
    omega
  have hcode : patternCode (g • fromCode representatives[r.val]!) = patternCode x := by
    change patternCode (tableAction4 v c • fromCode representatives[r.val]!) = _
    rw [tableAction_code,← transformed_components r v c,hp]
    exact hw
  have hrec : fromCode (patternCode (g • fromCode representatives[r.val]!)) =
      g • fromCode representatives[r.val]! := by
    exact reconstruct _
      (transport_symmetric colorGroup g _ (fromCode_symmetric _))
      (transport_no_loops colorGroup g _ (fromCode_no_loops _))
      (transport_full colorGroup g _ (fromCode_full _))
  refine ⟨r,g,?_⟩
  calc
    g • fromCode representatives[r.val]! = fromCode (patternCode (g • fromCode representatives[r.val]!)) := hrec.symm
    _ = fromCode (patternCode x) := congrArg fromCode hcode
    _ = x := reconstruct x hs hd hf
end ColeskiFourNormalization
#print axioms ColeskiFourNormalization.normalize

/- END bundled local module FourNormalization -/

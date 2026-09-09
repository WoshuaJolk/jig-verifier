import Commons.ColeskiE811Sig20260909_WitnessAction
import Commons.ColeskiE811Sig20260909_OrbitCoefficient
import Commons.ColeskiE811Sig20260909_PaletteFlags
import Commons.ColeskiE811Sig20260909_K6Check

/- BEGIN bundled local module WitnessCoefficient -/

namespace ColeskiWitnessCoefficient
open ColeskiPatternCode ColeskiK5Coverage ColeskiPaletteAction ColeskiPaletteFlags
open ColeskiWitnessAction ColeskiOrbitCoefficient ColeskiOrbitSeparation ColeskiOrbitStabilizers
open ColeskiOrbitChecks ColeskiK6Check
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem coefficient_witness
    (checks : ∀ r : Fin 551, ∀ k : Fin 7200, orbitCheck r.val k.val = true)
    (w : Fin 3967200) (n : Nat) (h : transformed5 (w.val+1) = n)
    (f : Fin 5 × Fin 6) :
    coefficientFor (fromCode n) f = (flagWeight (w.val+1) f.1.val f.2.val : ℝ) := by
  have hg : witnessAction w • representative (repIndex w) = fromCode n := witnessAction_eq w n h
  rw [coefficientFor_eq checks (repIndex w) (witnessAction w) (fromCode n) f hg]
  unfold coefficient
  change (weight (repIndex w).val
    ((tableAction (vertexIndex w) (colorIndex w))⁻¹ • f).1.val
    ((tableAction (vertexIndex w) (colorIndex w))⁻¹ • f).2.val : ℝ) - 170 = _
  rw [(inverse_flag_values (vertexIndex w) (colorIndex w) f).1,
    (inverse_flag_values (vertexIndex w) (colorIndex w) f).2]
  simp only [flagWeight, Nat.add_sub_cancel, repIndex,vertexIndex,colorIndex,
    Int.cast_sub,Int.cast_natCast,Int.cast_ofNat]
end ColeskiWitnessCoefficient
#print axioms ColeskiWitnessCoefficient.coefficient_witness

/- END bundled local module WitnessCoefficient -/

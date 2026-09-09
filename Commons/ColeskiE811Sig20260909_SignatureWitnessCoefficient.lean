import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions
import Commons.ColeskiE811Sig20260909_WitnessAction
import Commons.ColeskiE811Sig20260909_PaletteFlags
import Commons.ColeskiE811Sig20260909_K6Check

/- BEGIN bundled local module SignatureWitnessCoefficient -/


namespace ColeskiSignatureWitnessCoefficient

open ColeskiPatternAction ColeskiPatternCode ColeskiK5Coverage ColeskiPaletteAction
open ColeskiPaletteFlags ColeskiWitnessAction ColeskiK6Check ColeskiOrbitChecks
open ColeskiFlagSignature ColeskiSignatureWeights ColeskiSignatureRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem coefficient_witness
    (rows : ∀ r : Fin 551, rowMatches r)
    (w : Fin 3967200) (n : Nat) (h : transformed5 (w.val + 1) = n)
    (flag : FiveFlag) :
    coefficientFor (fromCode n) flag =
      (flagWeight (w.val + 1) flag.1.val flag.2.val : ℝ) := by
  have hg : witnessAction w • fromCode representatives5[(repIndex w).val]! = fromCode n :=
    witnessAction_eq w n h
  calc
    coefficientFor (fromCode n) flag =
        coefficientFor (fromCode representatives5[(repIndex w).val]!)
          ((witnessAction w)⁻¹ • flag) := by
      have ht := coefficientFor_transport (witnessAction w)
        (fromCode representatives5[(repIndex w).val]!) ((witnessAction w)⁻¹ • flag)
      simpa only [hg, smul_inv_smul] using ht
    _ = (weight (repIndex w).val
          ((witnessAction w)⁻¹ • flag).1.val
          ((witnessAction w)⁻¹ • flag).2.val : ℝ) - 170 :=
      coefficient_from_row (repIndex w) (rows (repIndex w)) _
    _ = (flagWeight (w.val + 1) flag.1.val flag.2.val : ℝ) := by
      unfold witnessAction
      rw [(inverse_flag_values (vertexIndex w) (colorIndex w) flag).1,
        (inverse_flag_values (vertexIndex w) (colorIndex w) flag).2]
      simp only [flagWeight, Nat.add_sub_cancel, repIndex, vertexIndex, colorIndex,
        Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]

end ColeskiSignatureWitnessCoefficient

#print axioms ColeskiSignatureWitnessCoefficient.coefficient_witness

/- END bundled local module SignatureWitnessCoefficient -/

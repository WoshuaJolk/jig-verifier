import Commons.ColeskiE811Sig20260909_SignatureWeights
import Commons.ColeskiE811Sig20260909_OrbitChecks

/- BEGIN bundled local module SignatureRowDefinitions -/


namespace ColeskiSignatureRows

open ColeskiFlagSignature ColeskiSignatureWeights
open ColeskiK5Coverage ColeskiPatternCode ColeskiOrbitChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def flagAt (i : Fin 30) : FiveFlag :=
  (⟨i.val / 6, by omega⟩, ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩)

def rowMatches (r : Fin 551) : Prop :=
  ∀ i : Fin 30,
    signatureWeight (signature (fromCode representatives5[r.val]!) (flagAt i)) =
      (weight r.val (i.val / 6) (i.val % 6) : Int) - 170

theorem flagAt_index (flag : FiveFlag) :
    flagAt ⟨6 * flag.1.val + flag.2.val, by omega⟩ = flag := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [flagAt]
  · omega
  · omega

theorem coefficient_from_row (r : Fin 551) (h : rowMatches r)
    (flag : FiveFlag) :
    coefficientFor (fromCode representatives5[r.val]!) flag =
      (weight r.val flag.1.val flag.2.val : ℝ) - 170 := by
  let i : Fin 30 := ⟨6 * flag.1.val + flag.2.val, by omega⟩
  have hf : flagAt i = flag := flagAt_index flag
  have hi1 : i.val / 6 = flag.1.val := by dsimp [i]; omega
  have hi2 : i.val % 6 = flag.2.val := by dsimp [i]; omega
  have hint : signatureWeight (signature (fromCode representatives5[r.val]!) flag) =
      (weight r.val flag.1.val flag.2.val : Int) - 170 := by
    simpa only [rowMatches, hf, hi1, hi2] using h i
  unfold coefficientFor
  calc
    (signatureWeight (signature (fromCode representatives5[r.val]!) flag) : ℝ) =
        (((weight r.val flag.1.val flag.2.val : Int) - 170 : Int) : ℝ) :=
      congrArg (fun z : Int => (z : ℝ)) hint
    _ = (weight r.val flag.1.val flag.2.val : ℝ) - 170 := by norm_num

end ColeskiSignatureRows

#print axioms ColeskiSignatureRows.coefficient_from_row

/- END bundled local module SignatureRowDefinitions -/

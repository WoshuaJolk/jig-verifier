import Commons.ColeskiE811Sig20260909_EdgeIndexTable

/- BEGIN bundled local module PatternTransformNumeric -/


namespace ColeskiPatternTransform

open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar ColeskiTablePermutations

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numericEdge (r v c : Nat) (e : Fin 10) : Fin 6 :=
  ⟨digit c (digit r (v / 10 ^ e.val % 10)), Nat.mod_lt _ (by decide)⟩

theorem transformCode_encode (r v c : Nat) :
    transformCode r v c = encode10 (numericEdge r v c) := by
  unfold transformCode
  have hstep :
      (fun acc i => acc + digit c (digit r (v / 10 ^ i % 10)) * 6 ^ i) =
      (fun acc i => acc + 6 ^ i * digit c (digit r (v / 10 ^ i % 10))) := by
    funext acc i
    rw [Nat.mul_comm (digit c (digit r (v / 10 ^ i % 10))) (6 ^ i)]
  rw [hstep]
  change 0 + 1 * (numericEdge r v c 0).val + 6 * (numericEdge r v c 1).val +
    36 * (numericEdge r v c 2).val + 216 * (numericEdge r v c 3).val +
    1296 * (numericEdge r v c 4).val + 7776 * (numericEdge r v c 5).val +
    46656 * (numericEdge r v c 6).val + 279936 * (numericEdge r v c 7).val +
    1679616 * (numericEdge r v c 8).val + 10077696 * (numericEdge r v c 9).val =
    (numericEdge r v c 0).val + 6 * (numericEdge r v c 1).val +
    36 * (numericEdge r v c 2).val + 216 * (numericEdge r v c 3).val +
    1296 * (numericEdge r v c 4).val + 7776 * (numericEdge r v c 5).val +
    46656 * (numericEdge r v c 6).val + 279936 * (numericEdge r v c 7).val +
    1679616 * (numericEdge r v c 8).val + 10077696 * (numericEdge r v c 9).val
  simp only [Nat.one_mul, Nat.zero_add]

end ColeskiPatternTransform

#print axioms ColeskiPatternTransform.transformCode_encode

/- END bundled local module PatternTransformNumeric -/

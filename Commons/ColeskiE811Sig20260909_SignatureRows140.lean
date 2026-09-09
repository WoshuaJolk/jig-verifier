import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows140 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block140

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row140 : rowMatches 140 := by
  intro i
  fin_cases i <;> decide

theorem row141 : rowMatches 141 := by
  intro i
  fin_cases i <;> decide

theorem row142 : rowMatches 142 := by
  intro i
  fin_cases i <;> decide

theorem row143 : rowMatches 143 := by
  intro i
  fin_cases i <;> decide

theorem row144 : rowMatches 144 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block140

/- END bundled local module SignatureRows140 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows255 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block255

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row255 : rowMatches 255 := by
  intro i
  fin_cases i <;> decide

theorem row256 : rowMatches 256 := by
  intro i
  fin_cases i <;> decide

theorem row257 : rowMatches 257 := by
  intro i
  fin_cases i <;> decide

theorem row258 : rowMatches 258 := by
  intro i
  fin_cases i <;> decide

theorem row259 : rowMatches 259 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block255

/- END bundled local module SignatureRows255 -/

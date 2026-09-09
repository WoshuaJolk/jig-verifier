import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows400 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block400

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row400 : rowMatches 400 := by
  intro i
  fin_cases i <;> decide

theorem row401 : rowMatches 401 := by
  intro i
  fin_cases i <;> decide

theorem row402 : rowMatches 402 := by
  intro i
  fin_cases i <;> decide

theorem row403 : rowMatches 403 := by
  intro i
  fin_cases i <;> decide

theorem row404 : rowMatches 404 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block400

/- END bundled local module SignatureRows400 -/

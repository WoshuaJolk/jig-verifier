import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows250 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block250

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row250 : rowMatches 250 := by
  intro i
  fin_cases i <;> decide

theorem row251 : rowMatches 251 := by
  intro i
  fin_cases i <;> decide

theorem row252 : rowMatches 252 := by
  intro i
  fin_cases i <;> decide

theorem row253 : rowMatches 253 := by
  intro i
  fin_cases i <;> decide

theorem row254 : rowMatches 254 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block250

/- END bundled local module SignatureRows250 -/

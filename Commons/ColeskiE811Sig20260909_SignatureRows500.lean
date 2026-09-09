import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows500 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block500

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row500 : rowMatches 500 := by
  intro i
  fin_cases i <;> decide

theorem row501 : rowMatches 501 := by
  intro i
  fin_cases i <;> decide

theorem row502 : rowMatches 502 := by
  intro i
  fin_cases i <;> decide

theorem row503 : rowMatches 503 := by
  intro i
  fin_cases i <;> decide

theorem row504 : rowMatches 504 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block500

/- END bundled local module SignatureRows500 -/

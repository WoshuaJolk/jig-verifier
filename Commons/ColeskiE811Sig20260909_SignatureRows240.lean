import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows240 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block240

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row240 : rowMatches 240 := by
  intro i
  fin_cases i <;> decide

theorem row241 : rowMatches 241 := by
  intro i
  fin_cases i <;> decide

theorem row242 : rowMatches 242 := by
  intro i
  fin_cases i <;> decide

theorem row243 : rowMatches 243 := by
  intro i
  fin_cases i <;> decide

theorem row244 : rowMatches 244 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block240

/- END bundled local module SignatureRows240 -/

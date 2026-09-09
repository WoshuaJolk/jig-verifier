import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows200 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block200

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row200 : rowMatches 200 := by
  intro i
  fin_cases i <;> decide

theorem row201 : rowMatches 201 := by
  intro i
  fin_cases i <;> decide

theorem row202 : rowMatches 202 := by
  intro i
  fin_cases i <;> decide

theorem row203 : rowMatches 203 := by
  intro i
  fin_cases i <;> decide

theorem row204 : rowMatches 204 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block200

/- END bundled local module SignatureRows200 -/

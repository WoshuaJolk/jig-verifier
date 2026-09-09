import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows360 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block360

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row360 : rowMatches 360 := by
  intro i
  fin_cases i <;> decide

theorem row361 : rowMatches 361 := by
  intro i
  fin_cases i <;> decide

theorem row362 : rowMatches 362 := by
  intro i
  fin_cases i <;> decide

theorem row363 : rowMatches 363 := by
  intro i
  fin_cases i <;> decide

theorem row364 : rowMatches 364 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block360

/- END bundled local module SignatureRows360 -/

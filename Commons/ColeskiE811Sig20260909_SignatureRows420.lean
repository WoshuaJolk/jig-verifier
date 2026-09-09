import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows420 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block420

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row420 : rowMatches 420 := by
  intro i
  fin_cases i <;> decide

theorem row421 : rowMatches 421 := by
  intro i
  fin_cases i <;> decide

theorem row422 : rowMatches 422 := by
  intro i
  fin_cases i <;> decide

theorem row423 : rowMatches 423 := by
  intro i
  fin_cases i <;> decide

theorem row424 : rowMatches 424 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block420

/- END bundled local module SignatureRows420 -/

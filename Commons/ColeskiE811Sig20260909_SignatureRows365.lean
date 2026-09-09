import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows365 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block365

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row365 : rowMatches 365 := by
  intro i
  fin_cases i <;> decide

theorem row366 : rowMatches 366 := by
  intro i
  fin_cases i <;> decide

theorem row367 : rowMatches 367 := by
  intro i
  fin_cases i <;> decide

theorem row368 : rowMatches 368 := by
  intro i
  fin_cases i <;> decide

theorem row369 : rowMatches 369 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block365

/- END bundled local module SignatureRows365 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows005 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block005

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row005 : rowMatches 5 := by
  intro i
  fin_cases i <;> decide

theorem row006 : rowMatches 6 := by
  intro i
  fin_cases i <;> decide

theorem row007 : rowMatches 7 := by
  intro i
  fin_cases i <;> decide

theorem row008 : rowMatches 8 := by
  intro i
  fin_cases i <;> decide

theorem row009 : rowMatches 9 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block005

/- END bundled local module SignatureRows005 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows010 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block010

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row010 : rowMatches 10 := by
  intro i
  fin_cases i <;> decide

theorem row011 : rowMatches 11 := by
  intro i
  fin_cases i <;> decide

theorem row012 : rowMatches 12 := by
  intro i
  fin_cases i <;> decide

theorem row013 : rowMatches 13 := by
  intro i
  fin_cases i <;> decide

theorem row014 : rowMatches 14 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block010

/- END bundled local module SignatureRows010 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows060 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block060

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row060 : rowMatches 60 := by
  intro i
  fin_cases i <;> decide

theorem row061 : rowMatches 61 := by
  intro i
  fin_cases i <;> decide

theorem row062 : rowMatches 62 := by
  intro i
  fin_cases i <;> decide

theorem row063 : rowMatches 63 := by
  intro i
  fin_cases i <;> decide

theorem row064 : rowMatches 64 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block060

/- END bundled local module SignatureRows060 -/

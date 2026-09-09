import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows120 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block120

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row120 : rowMatches 120 := by
  intro i
  fin_cases i <;> decide

theorem row121 : rowMatches 121 := by
  intro i
  fin_cases i <;> decide

theorem row122 : rowMatches 122 := by
  intro i
  fin_cases i <;> decide

theorem row123 : rowMatches 123 := by
  intro i
  fin_cases i <;> decide

theorem row124 : rowMatches 124 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block120

/- END bundled local module SignatureRows120 -/

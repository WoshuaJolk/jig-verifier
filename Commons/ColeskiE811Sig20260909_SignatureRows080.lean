import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows080 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block080

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row080 : rowMatches 80 := by
  intro i
  fin_cases i <;> decide

theorem row081 : rowMatches 81 := by
  intro i
  fin_cases i <;> decide

theorem row082 : rowMatches 82 := by
  intro i
  fin_cases i <;> decide

theorem row083 : rowMatches 83 := by
  intro i
  fin_cases i <;> decide

theorem row084 : rowMatches 84 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block080

/- END bundled local module SignatureRows080 -/

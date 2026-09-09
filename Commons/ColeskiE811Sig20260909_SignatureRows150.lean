import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows150 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block150

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row150 : rowMatches 150 := by
  intro i
  fin_cases i <;> decide

theorem row151 : rowMatches 151 := by
  intro i
  fin_cases i <;> decide

theorem row152 : rowMatches 152 := by
  intro i
  fin_cases i <;> decide

theorem row153 : rowMatches 153 := by
  intro i
  fin_cases i <;> decide

theorem row154 : rowMatches 154 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block150

/- END bundled local module SignatureRows150 -/

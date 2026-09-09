import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows180 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block180

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row180 : rowMatches 180 := by
  intro i
  fin_cases i <;> decide

theorem row181 : rowMatches 181 := by
  intro i
  fin_cases i <;> decide

theorem row182 : rowMatches 182 := by
  intro i
  fin_cases i <;> decide

theorem row183 : rowMatches 183 := by
  intro i
  fin_cases i <;> decide

theorem row184 : rowMatches 184 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block180

/- END bundled local module SignatureRows180 -/

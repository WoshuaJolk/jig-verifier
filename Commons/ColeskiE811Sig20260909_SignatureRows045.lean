import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows045 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block045

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row045 : rowMatches 45 := by
  intro i
  fin_cases i <;> decide

theorem row046 : rowMatches 46 := by
  intro i
  fin_cases i <;> decide

theorem row047 : rowMatches 47 := by
  intro i
  fin_cases i <;> decide

theorem row048 : rowMatches 48 := by
  intro i
  fin_cases i <;> decide

theorem row049 : rowMatches 49 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block045

/- END bundled local module SignatureRows045 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows030 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block030

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row030 : rowMatches 30 := by
  intro i
  fin_cases i <;> decide

theorem row031 : rowMatches 31 := by
  intro i
  fin_cases i <;> decide

theorem row032 : rowMatches 32 := by
  intro i
  fin_cases i <;> decide

theorem row033 : rowMatches 33 := by
  intro i
  fin_cases i <;> decide

theorem row034 : rowMatches 34 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block030

/- END bundled local module SignatureRows030 -/

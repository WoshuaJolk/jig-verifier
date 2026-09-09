import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows160 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block160

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row160 : rowMatches 160 := by
  intro i
  fin_cases i <;> decide

theorem row161 : rowMatches 161 := by
  intro i
  fin_cases i <;> decide

theorem row162 : rowMatches 162 := by
  intro i
  fin_cases i <;> decide

theorem row163 : rowMatches 163 := by
  intro i
  fin_cases i <;> decide

theorem row164 : rowMatches 164 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block160

/- END bundled local module SignatureRows160 -/

import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows000 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block000

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row000 : rowMatches 0 := by
  intro i
  fin_cases i <;> decide

theorem row001 : rowMatches 1 := by
  intro i
  fin_cases i <;> decide

theorem row002 : rowMatches 2 := by
  intro i
  fin_cases i <;> decide

theorem row003 : rowMatches 3 := by
  intro i
  fin_cases i <;> decide

theorem row004 : rowMatches 4 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block000

/- END bundled local module SignatureRows000 -/

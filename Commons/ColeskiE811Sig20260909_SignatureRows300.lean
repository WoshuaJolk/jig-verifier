import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows300 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block300

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row300 : rowMatches 300 := by
  intro i
  fin_cases i <;> decide

theorem row301 : rowMatches 301 := by
  intro i
  fin_cases i <;> decide

theorem row302 : rowMatches 302 := by
  intro i
  fin_cases i <;> decide

theorem row303 : rowMatches 303 := by
  intro i
  fin_cases i <;> decide

theorem row304 : rowMatches 304 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block300

/- END bundled local module SignatureRows300 -/

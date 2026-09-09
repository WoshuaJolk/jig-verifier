import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows025 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block025

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row025 : rowMatches 25 := by
  intro i
  fin_cases i <;> decide

theorem row026 : rowMatches 26 := by
  intro i
  fin_cases i <;> decide

theorem row027 : rowMatches 27 := by
  intro i
  fin_cases i <;> decide

theorem row028 : rowMatches 28 := by
  intro i
  fin_cases i <;> decide

theorem row029 : rowMatches 29 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block025

/- END bundled local module SignatureRows025 -/

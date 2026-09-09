import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows020 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block020

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row020 : rowMatches 20 := by
  intro i
  fin_cases i <;> decide

theorem row021 : rowMatches 21 := by
  intro i
  fin_cases i <;> decide

theorem row022 : rowMatches 22 := by
  intro i
  fin_cases i <;> decide

theorem row023 : rowMatches 23 := by
  intro i
  fin_cases i <;> decide

theorem row024 : rowMatches 24 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block020

/- END bundled local module SignatureRows020 -/

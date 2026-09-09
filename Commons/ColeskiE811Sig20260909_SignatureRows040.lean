import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows040 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block040

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row040 : rowMatches 40 := by
  intro i
  fin_cases i <;> decide

theorem row041 : rowMatches 41 := by
  intro i
  fin_cases i <;> decide

theorem row042 : rowMatches 42 := by
  intro i
  fin_cases i <;> decide

theorem row043 : rowMatches 43 := by
  intro i
  fin_cases i <;> decide

theorem row044 : rowMatches 44 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block040

/- END bundled local module SignatureRows040 -/

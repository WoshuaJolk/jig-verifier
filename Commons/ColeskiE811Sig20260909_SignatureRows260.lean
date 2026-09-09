import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows260 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block260

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row260 : rowMatches 260 := by
  intro i
  fin_cases i <;> decide

theorem row261 : rowMatches 261 := by
  intro i
  fin_cases i <;> decide

theorem row262 : rowMatches 262 := by
  intro i
  fin_cases i <;> decide

theorem row263 : rowMatches 263 := by
  intro i
  fin_cases i <;> decide

theorem row264 : rowMatches 264 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block260

/- END bundled local module SignatureRows260 -/

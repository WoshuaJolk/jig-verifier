import Commons.ColeskiE811Sig20260909_SignatureRowDefinitions

/- BEGIN bundled local module SignatureRows015 -/

-- Uses the balanced signature-weight dispatch generated in SignatureWeights.

namespace ColeskiSignatureRows.Block015

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row015 : rowMatches 15 := by
  intro i
  fin_cases i <;> decide

theorem row016 : rowMatches 16 := by
  intro i
  fin_cases i <;> decide

theorem row017 : rowMatches 17 := by
  intro i
  fin_cases i <;> decide

theorem row018 : rowMatches 18 := by
  intro i
  fin_cases i <;> decide

theorem row019 : rowMatches 19 := by
  intro i
  fin_cases i <;> decide

end ColeskiSignatureRows.Block015

/- END bundled local module SignatureRows015 -/

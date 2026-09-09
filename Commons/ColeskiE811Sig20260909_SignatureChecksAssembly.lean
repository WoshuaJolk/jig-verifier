import Commons.ColeskiE811Sig20260909_SignatureRowRange000
import Commons.ColeskiE811Sig20260909_PositiveRange000
import Commons.ColeskiE811Sig20260909_SignatureRowRange050
import Commons.ColeskiE811Sig20260909_PositiveRange050
import Commons.ColeskiE811Sig20260909_SignatureRowRange100
import Commons.ColeskiE811Sig20260909_PositiveRange100
import Commons.ColeskiE811Sig20260909_SignatureRowRange150
import Commons.ColeskiE811Sig20260909_PositiveRange150
import Commons.ColeskiE811Sig20260909_SignatureRowRange200
import Commons.ColeskiE811Sig20260909_PositiveRange200
import Commons.ColeskiE811Sig20260909_SignatureRowRange250
import Commons.ColeskiE811Sig20260909_PositiveRange250
import Commons.ColeskiE811Sig20260909_SignatureRowRange300
import Commons.ColeskiE811Sig20260909_PositiveRange300
import Commons.ColeskiE811Sig20260909_SignatureRowRange350
import Commons.ColeskiE811Sig20260909_PositiveRange350
import Commons.ColeskiE811Sig20260909_SignatureRowRange400
import Commons.ColeskiE811Sig20260909_PositiveRange400
import Commons.ColeskiE811Sig20260909_SignatureRowRange450
import Commons.ColeskiE811Sig20260909_PositiveRange450
import Commons.ColeskiE811Sig20260909_SignatureRowRange500
import Commons.ColeskiE811Sig20260909_PositiveRange500
import Commons.ColeskiE811Sig20260909_SignatureRowRange550
import Commons.ColeskiE811Sig20260909_PositiveRange550

/- BEGIN bundled local module SignatureChecksAssembly -/


namespace ColeskiSignatureChecksAssembly

open ColeskiSignatureRows ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem row_checks (r : Fin 551) : rowMatches r := by
  by_cases h0 : r.val < 50
  · exact ColeskiSignatureRowRange000.rows r (by omega) h0
  by_cases h1 : r.val < 100
  · exact ColeskiSignatureRowRange050.rows r (by omega) h1
  by_cases h2 : r.val < 150
  · exact ColeskiSignatureRowRange100.rows r (by omega) h2
  by_cases h3 : r.val < 200
  · exact ColeskiSignatureRowRange150.rows r (by omega) h3
  by_cases h4 : r.val < 250
  · exact ColeskiSignatureRowRange200.rows r (by omega) h4
  by_cases h5 : r.val < 300
  · exact ColeskiSignatureRowRange250.rows r (by omega) h5
  by_cases h6 : r.val < 350
  · exact ColeskiSignatureRowRange300.rows r (by omega) h6
  by_cases h7 : r.val < 400
  · exact ColeskiSignatureRowRange350.rows r (by omega) h7
  by_cases h8 : r.val < 450
  · exact ColeskiSignatureRowRange400.rows r (by omega) h8
  by_cases h9 : r.val < 500
  · exact ColeskiSignatureRowRange450.rows r (by omega) h9
  by_cases h10 : r.val < 550
  · exact ColeskiSignatureRowRange500.rows r (by omega) h10
  exact ColeskiSignatureRowRange550.rows r (by omega) r.isLt

theorem positivity (r : Fin 551) (a : Fin 7776)
    (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  by_cases h0 : r.val < 50
  · exact ColeskiPositiveRange000.rows r (by omega) h0 a ha
  by_cases h1 : r.val < 100
  · exact ColeskiPositiveRange050.rows r (by omega) h1 a ha
  by_cases h2 : r.val < 150
  · exact ColeskiPositiveRange100.rows r (by omega) h2 a ha
  by_cases h3 : r.val < 200
  · exact ColeskiPositiveRange150.rows r (by omega) h3 a ha
  by_cases h4 : r.val < 250
  · exact ColeskiPositiveRange200.rows r (by omega) h4 a ha
  by_cases h5 : r.val < 300
  · exact ColeskiPositiveRange250.rows r (by omega) h5 a ha
  by_cases h6 : r.val < 350
  · exact ColeskiPositiveRange300.rows r (by omega) h6 a ha
  by_cases h7 : r.val < 400
  · exact ColeskiPositiveRange350.rows r (by omega) h7 a ha
  by_cases h8 : r.val < 450
  · exact ColeskiPositiveRange400.rows r (by omega) h8 a ha
  by_cases h9 : r.val < 500
  · exact ColeskiPositiveRange450.rows r (by omega) h9 a ha
  by_cases h10 : r.val < 550
  · exact ColeskiPositiveRange500.rows r (by omega) h10 a ha
  exact ColeskiPositiveRange550.rows r (by omega) r.isLt a ha

end ColeskiSignatureChecksAssembly

#print axioms ColeskiSignatureChecksAssembly.row_checks
#print axioms ColeskiSignatureChecksAssembly.positivity

/- END bundled local module SignatureChecksAssembly -/

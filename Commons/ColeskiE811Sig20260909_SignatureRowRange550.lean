import Commons.ColeskiE811Sig20260909_SignatureRows550

/- BEGIN bundled local module SignatureRowRange550 -/


namespace ColeskiSignatureRowRange550

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hlo : 550 ≤ r.val) (hhi : r.val < 551) : rowMatches r := by
  have hr : r = 550 := by omega
  rcases hr with rfl
  · exact ColeskiSignatureRows.Block550.row550

end ColeskiSignatureRowRange550

/- END bundled local module SignatureRowRange550 -/

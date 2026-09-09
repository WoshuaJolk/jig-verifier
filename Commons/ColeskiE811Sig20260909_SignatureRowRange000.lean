import Commons.ColeskiE811Sig20260909_SignatureRows000
import Commons.ColeskiE811Sig20260909_SignatureRows005
import Commons.ColeskiE811Sig20260909_SignatureRows010
import Commons.ColeskiE811Sig20260909_SignatureRows015
import Commons.ColeskiE811Sig20260909_SignatureRows020
import Commons.ColeskiE811Sig20260909_SignatureRows025
import Commons.ColeskiE811Sig20260909_SignatureRows030
import Commons.ColeskiE811Sig20260909_SignatureRows035
import Commons.ColeskiE811Sig20260909_SignatureRows040
import Commons.ColeskiE811Sig20260909_SignatureRows045

/- BEGIN bundled local module SignatureRowRange000 -/


namespace ColeskiSignatureRowRange000

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hlo : 0 ≤ r.val) (hhi : r.val < 50) : rowMatches r := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 ∨ r = 32 ∨ r = 33 ∨ r = 34 ∨ r = 35 ∨ r = 36 ∨ r = 37 ∨ r = 38 ∨ r = 39 ∨ r = 40 ∨ r = 41 ∨ r = 42 ∨ r = 43 ∨ r = 44 ∨ r = 45 ∨ r = 46 ∨ r = 47 ∨ r = 48 ∨ r = 49 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiSignatureRows.Block000.row000
  · exact ColeskiSignatureRows.Block000.row001
  · exact ColeskiSignatureRows.Block000.row002
  · exact ColeskiSignatureRows.Block000.row003
  · exact ColeskiSignatureRows.Block000.row004
  · exact ColeskiSignatureRows.Block005.row005
  · exact ColeskiSignatureRows.Block005.row006
  · exact ColeskiSignatureRows.Block005.row007
  · exact ColeskiSignatureRows.Block005.row008
  · exact ColeskiSignatureRows.Block005.row009
  · exact ColeskiSignatureRows.Block010.row010
  · exact ColeskiSignatureRows.Block010.row011
  · exact ColeskiSignatureRows.Block010.row012
  · exact ColeskiSignatureRows.Block010.row013
  · exact ColeskiSignatureRows.Block010.row014
  · exact ColeskiSignatureRows.Block015.row015
  · exact ColeskiSignatureRows.Block015.row016
  · exact ColeskiSignatureRows.Block015.row017
  · exact ColeskiSignatureRows.Block015.row018
  · exact ColeskiSignatureRows.Block015.row019
  · exact ColeskiSignatureRows.Block020.row020
  · exact ColeskiSignatureRows.Block020.row021
  · exact ColeskiSignatureRows.Block020.row022
  · exact ColeskiSignatureRows.Block020.row023
  · exact ColeskiSignatureRows.Block020.row024
  · exact ColeskiSignatureRows.Block025.row025
  · exact ColeskiSignatureRows.Block025.row026
  · exact ColeskiSignatureRows.Block025.row027
  · exact ColeskiSignatureRows.Block025.row028
  · exact ColeskiSignatureRows.Block025.row029
  · exact ColeskiSignatureRows.Block030.row030
  · exact ColeskiSignatureRows.Block030.row031
  · exact ColeskiSignatureRows.Block030.row032
  · exact ColeskiSignatureRows.Block030.row033
  · exact ColeskiSignatureRows.Block030.row034
  · exact ColeskiSignatureRows.Block035.row035
  · exact ColeskiSignatureRows.Block035.row036
  · exact ColeskiSignatureRows.Block035.row037
  · exact ColeskiSignatureRows.Block035.row038
  · exact ColeskiSignatureRows.Block035.row039
  · exact ColeskiSignatureRows.Block040.row040
  · exact ColeskiSignatureRows.Block040.row041
  · exact ColeskiSignatureRows.Block040.row042
  · exact ColeskiSignatureRows.Block040.row043
  · exact ColeskiSignatureRows.Block040.row044
  · exact ColeskiSignatureRows.Block045.row045
  · exact ColeskiSignatureRows.Block045.row046
  · exact ColeskiSignatureRows.Block045.row047
  · exact ColeskiSignatureRows.Block045.row048
  · exact ColeskiSignatureRows.Block045.row049

end ColeskiSignatureRowRange000

/- END bundled local module SignatureRowRange000 -/

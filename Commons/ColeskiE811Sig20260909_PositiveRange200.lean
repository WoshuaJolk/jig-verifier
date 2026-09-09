import Commons.ColeskiE811Sig20260909_PositiveRowsGroup200
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup205
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup210
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup215
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup220
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup225
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup230
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup235
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup240
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup245

/- BEGIN bundled local module PositiveRange200 -/

namespace ColeskiPositiveRange200
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 200 ≤ r.val) (hu : r.val < 250)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 200 ∨ r = 201 ∨ r = 202 ∨ r = 203 ∨ r = 204 ∨ r = 205 ∨ r = 206 ∨ r = 207 ∨ r = 208 ∨ r = 209 ∨ r = 210 ∨ r = 211 ∨ r = 212 ∨ r = 213 ∨ r = 214 ∨ r = 215 ∨ r = 216 ∨ r = 217 ∨ r = 218 ∨ r = 219 ∨ r = 220 ∨ r = 221 ∨ r = 222 ∨ r = 223 ∨ r = 224 ∨ r = 225 ∨ r = 226 ∨ r = 227 ∨ r = 228 ∨ r = 229 ∨ r = 230 ∨ r = 231 ∨ r = 232 ∨ r = 233 ∨ r = 234 ∨ r = 235 ∨ r = 236 ∨ r = 237 ∨ r = 238 ∨ r = 239 ∨ r = 240 ∨ r = 241 ∨ r = 242 ∨ r = 243 ∨ r = 244 ∨ r = 245 ∨ r = 246 ∨ r = 247 ∨ r = 248 ∨ r = 249 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow200.row a ha
  · exact ColeskiPositiveRow201.row a ha
  · exact ColeskiPositiveRow202.row a ha
  · exact ColeskiPositiveRow203.row a ha
  · exact ColeskiPositiveRow204.row a ha
  · exact ColeskiPositiveRow205.row a ha
  · exact ColeskiPositiveRow206.row a ha
  · exact ColeskiPositiveRow207.row a ha
  · exact ColeskiPositiveRow208.row a ha
  · exact ColeskiPositiveRow209.row a ha
  · exact ColeskiPositiveRow210.row a ha
  · exact ColeskiPositiveRow211.row a ha
  · exact ColeskiPositiveRow212.row a ha
  · exact ColeskiPositiveRow213.row a ha
  · exact ColeskiPositiveRow214.row a ha
  · exact ColeskiPositiveRow215.row a ha
  · exact ColeskiPositiveRow216.row a ha
  · exact ColeskiPositiveRow217.row a ha
  · exact ColeskiPositiveRow218.row a ha
  · exact ColeskiPositiveRow219.row a ha
  · exact ColeskiPositiveRow220.row a ha
  · exact ColeskiPositiveRow221.row a ha
  · exact ColeskiPositiveRow222.row a ha
  · exact ColeskiPositiveRow223.row a ha
  · exact ColeskiPositiveRow224.row a ha
  · exact ColeskiPositiveRow225.row a ha
  · exact ColeskiPositiveRow226.row a ha
  · exact ColeskiPositiveRow227.row a ha
  · exact ColeskiPositiveRow228.row a ha
  · exact ColeskiPositiveRow229.row a ha
  · exact ColeskiPositiveRow230.row a ha
  · exact ColeskiPositiveRow231.row a ha
  · exact ColeskiPositiveRow232.row a ha
  · exact ColeskiPositiveRow233.row a ha
  · exact ColeskiPositiveRow234.row a ha
  · exact ColeskiPositiveRow235.row a ha
  · exact ColeskiPositiveRow236.row a ha
  · exact ColeskiPositiveRow237.row a ha
  · exact ColeskiPositiveRow238.row a ha
  · exact ColeskiPositiveRow239.row a ha
  · exact ColeskiPositiveRow240.row a ha
  · exact ColeskiPositiveRow241.row a ha
  · exact ColeskiPositiveRow242.row a ha
  · exact ColeskiPositiveRow243.row a ha
  · exact ColeskiPositiveRow244.row a ha
  · exact ColeskiPositiveRow245.row a ha
  · exact ColeskiPositiveRow246.row a ha
  · exact ColeskiPositiveRow247.row a ha
  · exact ColeskiPositiveRow248.row a ha
  · exact ColeskiPositiveRow249.row a ha
end ColeskiPositiveRange200
#print axioms ColeskiPositiveRange200.rows

/- END bundled local module PositiveRange200 -/

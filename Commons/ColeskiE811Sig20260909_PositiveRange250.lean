import Commons.ColeskiE811Sig20260909_PositiveRowsGroup250
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup255
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup260
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup265
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup270
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup275
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup280
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup285
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup290
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup295

/- BEGIN bundled local module PositiveRange250 -/

namespace ColeskiPositiveRange250
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 250 ≤ r.val) (hu : r.val < 300)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 250 ∨ r = 251 ∨ r = 252 ∨ r = 253 ∨ r = 254 ∨ r = 255 ∨ r = 256 ∨ r = 257 ∨ r = 258 ∨ r = 259 ∨ r = 260 ∨ r = 261 ∨ r = 262 ∨ r = 263 ∨ r = 264 ∨ r = 265 ∨ r = 266 ∨ r = 267 ∨ r = 268 ∨ r = 269 ∨ r = 270 ∨ r = 271 ∨ r = 272 ∨ r = 273 ∨ r = 274 ∨ r = 275 ∨ r = 276 ∨ r = 277 ∨ r = 278 ∨ r = 279 ∨ r = 280 ∨ r = 281 ∨ r = 282 ∨ r = 283 ∨ r = 284 ∨ r = 285 ∨ r = 286 ∨ r = 287 ∨ r = 288 ∨ r = 289 ∨ r = 290 ∨ r = 291 ∨ r = 292 ∨ r = 293 ∨ r = 294 ∨ r = 295 ∨ r = 296 ∨ r = 297 ∨ r = 298 ∨ r = 299 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow250.row a ha
  · exact ColeskiPositiveRow251.row a ha
  · exact ColeskiPositiveRow252.row a ha
  · exact ColeskiPositiveRow253.row a ha
  · exact ColeskiPositiveRow254.row a ha
  · exact ColeskiPositiveRow255.row a ha
  · exact ColeskiPositiveRow256.row a ha
  · exact ColeskiPositiveRow257.row a ha
  · exact ColeskiPositiveRow258.row a ha
  · exact ColeskiPositiveRow259.row a ha
  · exact ColeskiPositiveRow260.row a ha
  · exact ColeskiPositiveRow261.row a ha
  · exact ColeskiPositiveRow262.row a ha
  · exact ColeskiPositiveRow263.row a ha
  · exact ColeskiPositiveRow264.row a ha
  · exact ColeskiPositiveRow265.row a ha
  · exact ColeskiPositiveRow266.row a ha
  · exact ColeskiPositiveRow267.row a ha
  · exact ColeskiPositiveRow268.row a ha
  · exact ColeskiPositiveRow269.row a ha
  · exact ColeskiPositiveRow270.row a ha
  · exact ColeskiPositiveRow271.row a ha
  · exact ColeskiPositiveRow272.row a ha
  · exact ColeskiPositiveRow273.row a ha
  · exact ColeskiPositiveRow274.row a ha
  · exact ColeskiPositiveRow275.row a ha
  · exact ColeskiPositiveRow276.row a ha
  · exact ColeskiPositiveRow277.row a ha
  · exact ColeskiPositiveRow278.row a ha
  · exact ColeskiPositiveRow279.row a ha
  · exact ColeskiPositiveRow280.row a ha
  · exact ColeskiPositiveRow281.row a ha
  · exact ColeskiPositiveRow282.row a ha
  · exact ColeskiPositiveRow283.row a ha
  · exact ColeskiPositiveRow284.row a ha
  · exact ColeskiPositiveRow285.row a ha
  · exact ColeskiPositiveRow286.row a ha
  · exact ColeskiPositiveRow287.row a ha
  · exact ColeskiPositiveRow288.row a ha
  · exact ColeskiPositiveRow289.row a ha
  · exact ColeskiPositiveRow290.row a ha
  · exact ColeskiPositiveRow291.row a ha
  · exact ColeskiPositiveRow292.row a ha
  · exact ColeskiPositiveRow293.row a ha
  · exact ColeskiPositiveRow294.row a ha
  · exact ColeskiPositiveRow295.row a ha
  · exact ColeskiPositiveRow296.row a ha
  · exact ColeskiPositiveRow297.row a ha
  · exact ColeskiPositiveRow298.row a ha
  · exact ColeskiPositiveRow299.row a ha
end ColeskiPositiveRange250
#print axioms ColeskiPositiveRange250.rows

/- END bundled local module PositiveRange250 -/

import Commons.ColeskiE811Sig20260909_PositiveRowsGroup300
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup305
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup310
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup315
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup320
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup325
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup330
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup335
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup340
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup345

/- BEGIN bundled local module PositiveRange300 -/

namespace ColeskiPositiveRange300
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 300 ≤ r.val) (hu : r.val < 350)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 300 ∨ r = 301 ∨ r = 302 ∨ r = 303 ∨ r = 304 ∨ r = 305 ∨ r = 306 ∨ r = 307 ∨ r = 308 ∨ r = 309 ∨ r = 310 ∨ r = 311 ∨ r = 312 ∨ r = 313 ∨ r = 314 ∨ r = 315 ∨ r = 316 ∨ r = 317 ∨ r = 318 ∨ r = 319 ∨ r = 320 ∨ r = 321 ∨ r = 322 ∨ r = 323 ∨ r = 324 ∨ r = 325 ∨ r = 326 ∨ r = 327 ∨ r = 328 ∨ r = 329 ∨ r = 330 ∨ r = 331 ∨ r = 332 ∨ r = 333 ∨ r = 334 ∨ r = 335 ∨ r = 336 ∨ r = 337 ∨ r = 338 ∨ r = 339 ∨ r = 340 ∨ r = 341 ∨ r = 342 ∨ r = 343 ∨ r = 344 ∨ r = 345 ∨ r = 346 ∨ r = 347 ∨ r = 348 ∨ r = 349 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow300.row a ha
  · exact ColeskiPositiveRow301.row a ha
  · exact ColeskiPositiveRow302.row a ha
  · exact ColeskiPositiveRow303.row a ha
  · exact ColeskiPositiveRow304.row a ha
  · exact ColeskiPositiveRow305.row a ha
  · exact ColeskiPositiveRow306.row a ha
  · exact ColeskiPositiveRow307.row a ha
  · exact ColeskiPositiveRow308.row a ha
  · exact ColeskiPositiveRow309.row a ha
  · exact ColeskiPositiveRow310.row a ha
  · exact ColeskiPositiveRow311.row a ha
  · exact ColeskiPositiveRow312.row a ha
  · exact ColeskiPositiveRow313.row a ha
  · exact ColeskiPositiveRow314.row a ha
  · exact ColeskiPositiveRow315.row a ha
  · exact ColeskiPositiveRow316.row a ha
  · exact ColeskiPositiveRow317.row a ha
  · exact ColeskiPositiveRow318.row a ha
  · exact ColeskiPositiveRow319.row a ha
  · exact ColeskiPositiveRow320.row a ha
  · exact ColeskiPositiveRow321.row a ha
  · exact ColeskiPositiveRow322.row a ha
  · exact ColeskiPositiveRow323.row a ha
  · exact ColeskiPositiveRow324.row a ha
  · exact ColeskiPositiveRow325.row a ha
  · exact ColeskiPositiveRow326.row a ha
  · exact ColeskiPositiveRow327.row a ha
  · exact ColeskiPositiveRow328.row a ha
  · exact ColeskiPositiveRow329.row a ha
  · exact ColeskiPositiveRow330.row a ha
  · exact ColeskiPositiveRow331.row a ha
  · exact ColeskiPositiveRow332.row a ha
  · exact ColeskiPositiveRow333.row a ha
  · exact ColeskiPositiveRow334.row a ha
  · exact ColeskiPositiveRow335.row a ha
  · exact ColeskiPositiveRow336.row a ha
  · exact ColeskiPositiveRow337.row a ha
  · exact ColeskiPositiveRow338.row a ha
  · exact ColeskiPositiveRow339.row a ha
  · exact ColeskiPositiveRow340.row a ha
  · exact ColeskiPositiveRow341.row a ha
  · exact ColeskiPositiveRow342.row a ha
  · exact ColeskiPositiveRow343.row a ha
  · exact ColeskiPositiveRow344.row a ha
  · exact ColeskiPositiveRow345.row a ha
  · exact ColeskiPositiveRow346.row a ha
  · exact ColeskiPositiveRow347.row a ha
  · exact ColeskiPositiveRow348.row a ha
  · exact ColeskiPositiveRow349.row a ha
end ColeskiPositiveRange300
#print axioms ColeskiPositiveRange300.rows

/- END bundled local module PositiveRange300 -/

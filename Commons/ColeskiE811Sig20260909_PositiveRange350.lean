import Commons.ColeskiE811Sig20260909_PositiveRowsGroup350
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup355
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup360
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup365
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup370
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup375
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup380
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup385
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup390
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup395

/- BEGIN bundled local module PositiveRange350 -/

namespace ColeskiPositiveRange350
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 350 ≤ r.val) (hu : r.val < 400)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 350 ∨ r = 351 ∨ r = 352 ∨ r = 353 ∨ r = 354 ∨ r = 355 ∨ r = 356 ∨ r = 357 ∨ r = 358 ∨ r = 359 ∨ r = 360 ∨ r = 361 ∨ r = 362 ∨ r = 363 ∨ r = 364 ∨ r = 365 ∨ r = 366 ∨ r = 367 ∨ r = 368 ∨ r = 369 ∨ r = 370 ∨ r = 371 ∨ r = 372 ∨ r = 373 ∨ r = 374 ∨ r = 375 ∨ r = 376 ∨ r = 377 ∨ r = 378 ∨ r = 379 ∨ r = 380 ∨ r = 381 ∨ r = 382 ∨ r = 383 ∨ r = 384 ∨ r = 385 ∨ r = 386 ∨ r = 387 ∨ r = 388 ∨ r = 389 ∨ r = 390 ∨ r = 391 ∨ r = 392 ∨ r = 393 ∨ r = 394 ∨ r = 395 ∨ r = 396 ∨ r = 397 ∨ r = 398 ∨ r = 399 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow350.row a ha
  · exact ColeskiPositiveRow351.row a ha
  · exact ColeskiPositiveRow352.row a ha
  · exact ColeskiPositiveRow353.row a ha
  · exact ColeskiPositiveRow354.row a ha
  · exact ColeskiPositiveRow355.row a ha
  · exact ColeskiPositiveRow356.row a ha
  · exact ColeskiPositiveRow357.row a ha
  · exact ColeskiPositiveRow358.row a ha
  · exact ColeskiPositiveRow359.row a ha
  · exact ColeskiPositiveRow360.row a ha
  · exact ColeskiPositiveRow361.row a ha
  · exact ColeskiPositiveRow362.row a ha
  · exact ColeskiPositiveRow363.row a ha
  · exact ColeskiPositiveRow364.row a ha
  · exact ColeskiPositiveRow365.row a ha
  · exact ColeskiPositiveRow366.row a ha
  · exact ColeskiPositiveRow367.row a ha
  · exact ColeskiPositiveRow368.row a ha
  · exact ColeskiPositiveRow369.row a ha
  · exact ColeskiPositiveRow370.row a ha
  · exact ColeskiPositiveRow371.row a ha
  · exact ColeskiPositiveRow372.row a ha
  · exact ColeskiPositiveRow373.row a ha
  · exact ColeskiPositiveRow374.row a ha
  · exact ColeskiPositiveRow375.row a ha
  · exact ColeskiPositiveRow376.row a ha
  · exact ColeskiPositiveRow377.row a ha
  · exact ColeskiPositiveRow378.row a ha
  · exact ColeskiPositiveRow379.row a ha
  · exact ColeskiPositiveRow380.row a ha
  · exact ColeskiPositiveRow381.row a ha
  · exact ColeskiPositiveRow382.row a ha
  · exact ColeskiPositiveRow383.row a ha
  · exact ColeskiPositiveRow384.row a ha
  · exact ColeskiPositiveRow385.row a ha
  · exact ColeskiPositiveRow386.row a ha
  · exact ColeskiPositiveRow387.row a ha
  · exact ColeskiPositiveRow388.row a ha
  · exact ColeskiPositiveRow389.row a ha
  · exact ColeskiPositiveRow390.row a ha
  · exact ColeskiPositiveRow391.row a ha
  · exact ColeskiPositiveRow392.row a ha
  · exact ColeskiPositiveRow393.row a ha
  · exact ColeskiPositiveRow394.row a ha
  · exact ColeskiPositiveRow395.row a ha
  · exact ColeskiPositiveRow396.row a ha
  · exact ColeskiPositiveRow397.row a ha
  · exact ColeskiPositiveRow398.row a ha
  · exact ColeskiPositiveRow399.row a ha
end ColeskiPositiveRange350
#print axioms ColeskiPositiveRange350.rows

/- END bundled local module PositiveRange350 -/

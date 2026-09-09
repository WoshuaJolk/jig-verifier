import Commons.ColeskiE811Sig20260909_PositiveRowsGroup450
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup455
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup460
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup465
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup470
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup475
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup480
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup485
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup490
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup495

/- BEGIN bundled local module PositiveRange450 -/

namespace ColeskiPositiveRange450
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 450 ≤ r.val) (hu : r.val < 500)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 450 ∨ r = 451 ∨ r = 452 ∨ r = 453 ∨ r = 454 ∨ r = 455 ∨ r = 456 ∨ r = 457 ∨ r = 458 ∨ r = 459 ∨ r = 460 ∨ r = 461 ∨ r = 462 ∨ r = 463 ∨ r = 464 ∨ r = 465 ∨ r = 466 ∨ r = 467 ∨ r = 468 ∨ r = 469 ∨ r = 470 ∨ r = 471 ∨ r = 472 ∨ r = 473 ∨ r = 474 ∨ r = 475 ∨ r = 476 ∨ r = 477 ∨ r = 478 ∨ r = 479 ∨ r = 480 ∨ r = 481 ∨ r = 482 ∨ r = 483 ∨ r = 484 ∨ r = 485 ∨ r = 486 ∨ r = 487 ∨ r = 488 ∨ r = 489 ∨ r = 490 ∨ r = 491 ∨ r = 492 ∨ r = 493 ∨ r = 494 ∨ r = 495 ∨ r = 496 ∨ r = 497 ∨ r = 498 ∨ r = 499 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow450.row a ha
  · exact ColeskiPositiveRow451.row a ha
  · exact ColeskiPositiveRow452.row a ha
  · exact ColeskiPositiveRow453.row a ha
  · exact ColeskiPositiveRow454.row a ha
  · exact ColeskiPositiveRow455.row a ha
  · exact ColeskiPositiveRow456.row a ha
  · exact ColeskiPositiveRow457.row a ha
  · exact ColeskiPositiveRow458.row a ha
  · exact ColeskiPositiveRow459.row a ha
  · exact ColeskiPositiveRow460.row a ha
  · exact ColeskiPositiveRow461.row a ha
  · exact ColeskiPositiveRow462.row a ha
  · exact ColeskiPositiveRow463.row a ha
  · exact ColeskiPositiveRow464.row a ha
  · exact ColeskiPositiveRow465.row a ha
  · exact ColeskiPositiveRow466.row a ha
  · exact ColeskiPositiveRow467.row a ha
  · exact ColeskiPositiveRow468.row a ha
  · exact ColeskiPositiveRow469.row a ha
  · exact ColeskiPositiveRow470.row a ha
  · exact ColeskiPositiveRow471.row a ha
  · exact ColeskiPositiveRow472.row a ha
  · exact ColeskiPositiveRow473.row a ha
  · exact ColeskiPositiveRow474.row a ha
  · exact ColeskiPositiveRow475.row a ha
  · exact ColeskiPositiveRow476.row a ha
  · exact ColeskiPositiveRow477.row a ha
  · exact ColeskiPositiveRow478.row a ha
  · exact ColeskiPositiveRow479.row a ha
  · exact ColeskiPositiveRow480.row a ha
  · exact ColeskiPositiveRow481.row a ha
  · exact ColeskiPositiveRow482.row a ha
  · exact ColeskiPositiveRow483.row a ha
  · exact ColeskiPositiveRow484.row a ha
  · exact ColeskiPositiveRow485.row a ha
  · exact ColeskiPositiveRow486.row a ha
  · exact ColeskiPositiveRow487.row a ha
  · exact ColeskiPositiveRow488.row a ha
  · exact ColeskiPositiveRow489.row a ha
  · exact ColeskiPositiveRow490.row a ha
  · exact ColeskiPositiveRow491.row a ha
  · exact ColeskiPositiveRow492.row a ha
  · exact ColeskiPositiveRow493.row a ha
  · exact ColeskiPositiveRow494.row a ha
  · exact ColeskiPositiveRow495.row a ha
  · exact ColeskiPositiveRow496.row a ha
  · exact ColeskiPositiveRow497.row a ha
  · exact ColeskiPositiveRow498.row a ha
  · exact ColeskiPositiveRow499.row a ha
end ColeskiPositiveRange450
#print axioms ColeskiPositiveRange450.rows

/- END bundled local module PositiveRange450 -/

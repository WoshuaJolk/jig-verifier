import Commons.ColeskiE811Sig20260909_PositiveRowsGroup500
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup505
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup510
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup515
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup520
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup525
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup530
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup535
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup540
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup545

/- BEGIN bundled local module PositiveRange500 -/

namespace ColeskiPositiveRange500
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 500 ≤ r.val) (hu : r.val < 550)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 500 ∨ r = 501 ∨ r = 502 ∨ r = 503 ∨ r = 504 ∨ r = 505 ∨ r = 506 ∨ r = 507 ∨ r = 508 ∨ r = 509 ∨ r = 510 ∨ r = 511 ∨ r = 512 ∨ r = 513 ∨ r = 514 ∨ r = 515 ∨ r = 516 ∨ r = 517 ∨ r = 518 ∨ r = 519 ∨ r = 520 ∨ r = 521 ∨ r = 522 ∨ r = 523 ∨ r = 524 ∨ r = 525 ∨ r = 526 ∨ r = 527 ∨ r = 528 ∨ r = 529 ∨ r = 530 ∨ r = 531 ∨ r = 532 ∨ r = 533 ∨ r = 534 ∨ r = 535 ∨ r = 536 ∨ r = 537 ∨ r = 538 ∨ r = 539 ∨ r = 540 ∨ r = 541 ∨ r = 542 ∨ r = 543 ∨ r = 544 ∨ r = 545 ∨ r = 546 ∨ r = 547 ∨ r = 548 ∨ r = 549 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow500.row a ha
  · exact ColeskiPositiveRow501.row a ha
  · exact ColeskiPositiveRow502.row a ha
  · exact ColeskiPositiveRow503.row a ha
  · exact ColeskiPositiveRow504.row a ha
  · exact ColeskiPositiveRow505.row a ha
  · exact ColeskiPositiveRow506.row a ha
  · exact ColeskiPositiveRow507.row a ha
  · exact ColeskiPositiveRow508.row a ha
  · exact ColeskiPositiveRow509.row a ha
  · exact ColeskiPositiveRow510.row a ha
  · exact ColeskiPositiveRow511.row a ha
  · exact ColeskiPositiveRow512.row a ha
  · exact ColeskiPositiveRow513.row a ha
  · exact ColeskiPositiveRow514.row a ha
  · exact ColeskiPositiveRow515.row a ha
  · exact ColeskiPositiveRow516.row a ha
  · exact ColeskiPositiveRow517.row a ha
  · exact ColeskiPositiveRow518.row a ha
  · exact ColeskiPositiveRow519.row a ha
  · exact ColeskiPositiveRow520.row a ha
  · exact ColeskiPositiveRow521.row a ha
  · exact ColeskiPositiveRow522.row a ha
  · exact ColeskiPositiveRow523.row a ha
  · exact ColeskiPositiveRow524.row a ha
  · exact ColeskiPositiveRow525.row a ha
  · exact ColeskiPositiveRow526.row a ha
  · exact ColeskiPositiveRow527.row a ha
  · exact ColeskiPositiveRow528.row a ha
  · exact ColeskiPositiveRow529.row a ha
  · exact ColeskiPositiveRow530.row a ha
  · exact ColeskiPositiveRow531.row a ha
  · exact ColeskiPositiveRow532.row a ha
  · exact ColeskiPositiveRow533.row a ha
  · exact ColeskiPositiveRow534.row a ha
  · exact ColeskiPositiveRow535.row a ha
  · exact ColeskiPositiveRow536.row a ha
  · exact ColeskiPositiveRow537.row a ha
  · exact ColeskiPositiveRow538.row a ha
  · exact ColeskiPositiveRow539.row a ha
  · exact ColeskiPositiveRow540.row a ha
  · exact ColeskiPositiveRow541.row a ha
  · exact ColeskiPositiveRow542.row a ha
  · exact ColeskiPositiveRow543.row a ha
  · exact ColeskiPositiveRow544.row a ha
  · exact ColeskiPositiveRow545.row a ha
  · exact ColeskiPositiveRow546.row a ha
  · exact ColeskiPositiveRow547.row a ha
  · exact ColeskiPositiveRow548.row a ha
  · exact ColeskiPositiveRow549.row a ha
end ColeskiPositiveRange500
#print axioms ColeskiPositiveRange500.rows

/- END bundled local module PositiveRange500 -/

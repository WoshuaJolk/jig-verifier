import Commons.ColeskiE811Sig20260909_PositiveRowsGroup400
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup405
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup410
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup415
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup420
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup425
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup430
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup435
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup440
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup445

/- BEGIN bundled local module PositiveRange400 -/

namespace ColeskiPositiveRange400
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 400 ≤ r.val) (hu : r.val < 450)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 400 ∨ r = 401 ∨ r = 402 ∨ r = 403 ∨ r = 404 ∨ r = 405 ∨ r = 406 ∨ r = 407 ∨ r = 408 ∨ r = 409 ∨ r = 410 ∨ r = 411 ∨ r = 412 ∨ r = 413 ∨ r = 414 ∨ r = 415 ∨ r = 416 ∨ r = 417 ∨ r = 418 ∨ r = 419 ∨ r = 420 ∨ r = 421 ∨ r = 422 ∨ r = 423 ∨ r = 424 ∨ r = 425 ∨ r = 426 ∨ r = 427 ∨ r = 428 ∨ r = 429 ∨ r = 430 ∨ r = 431 ∨ r = 432 ∨ r = 433 ∨ r = 434 ∨ r = 435 ∨ r = 436 ∨ r = 437 ∨ r = 438 ∨ r = 439 ∨ r = 440 ∨ r = 441 ∨ r = 442 ∨ r = 443 ∨ r = 444 ∨ r = 445 ∨ r = 446 ∨ r = 447 ∨ r = 448 ∨ r = 449 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow400.row a ha
  · exact ColeskiPositiveRow401.row a ha
  · exact ColeskiPositiveRow402.row a ha
  · exact ColeskiPositiveRow403.row a ha
  · exact ColeskiPositiveRow404.row a ha
  · exact ColeskiPositiveRow405.row a ha
  · exact ColeskiPositiveRow406.row a ha
  · exact ColeskiPositiveRow407.row a ha
  · exact ColeskiPositiveRow408.row a ha
  · exact ColeskiPositiveRow409.row a ha
  · exact ColeskiPositiveRow410.row a ha
  · exact ColeskiPositiveRow411.row a ha
  · exact ColeskiPositiveRow412.row a ha
  · exact ColeskiPositiveRow413.row a ha
  · exact ColeskiPositiveRow414.row a ha
  · exact ColeskiPositiveRow415.row a ha
  · exact ColeskiPositiveRow416.row a ha
  · exact ColeskiPositiveRow417.row a ha
  · exact ColeskiPositiveRow418.row a ha
  · exact ColeskiPositiveRow419.row a ha
  · exact ColeskiPositiveRow420.row a ha
  · exact ColeskiPositiveRow421.row a ha
  · exact ColeskiPositiveRow422.row a ha
  · exact ColeskiPositiveRow423.row a ha
  · exact ColeskiPositiveRow424.row a ha
  · exact ColeskiPositiveRow425.row a ha
  · exact ColeskiPositiveRow426.row a ha
  · exact ColeskiPositiveRow427.row a ha
  · exact ColeskiPositiveRow428.row a ha
  · exact ColeskiPositiveRow429.row a ha
  · exact ColeskiPositiveRow430.row a ha
  · exact ColeskiPositiveRow431.row a ha
  · exact ColeskiPositiveRow432.row a ha
  · exact ColeskiPositiveRow433.row a ha
  · exact ColeskiPositiveRow434.row a ha
  · exact ColeskiPositiveRow435.row a ha
  · exact ColeskiPositiveRow436.row a ha
  · exact ColeskiPositiveRow437.row a ha
  · exact ColeskiPositiveRow438.row a ha
  · exact ColeskiPositiveRow439.row a ha
  · exact ColeskiPositiveRow440.row a ha
  · exact ColeskiPositiveRow441.row a ha
  · exact ColeskiPositiveRow442.row a ha
  · exact ColeskiPositiveRow443.row a ha
  · exact ColeskiPositiveRow444.row a ha
  · exact ColeskiPositiveRow445.row a ha
  · exact ColeskiPositiveRow446.row a ha
  · exact ColeskiPositiveRow447.row a ha
  · exact ColeskiPositiveRow448.row a ha
  · exact ColeskiPositiveRow449.row a ha
end ColeskiPositiveRange400
#print axioms ColeskiPositiveRange400.rows

/- END bundled local module PositiveRange400 -/

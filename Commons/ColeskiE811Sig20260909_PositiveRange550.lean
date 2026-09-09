import Commons.ColeskiE811Sig20260909_PositiveRowsGroup550

/- BEGIN bundled local module PositiveRange550 -/

namespace ColeskiPositiveRange550
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 550 ≤ r.val) (hu : r.val < 551)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 550 := by omega
  rcases hr with rfl
  · exact ColeskiPositiveRow550.row a ha
end ColeskiPositiveRange550
#print axioms ColeskiPositiveRange550.rows

/- END bundled local module PositiveRange550 -/

import Commons.ColeskiE811Sig20260909_PositiveRowsGroup000
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup005
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup010
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup015
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup020
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup025
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup030
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup035
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup040
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup045

/- BEGIN bundled local module PositiveRange000 -/

namespace ColeskiPositiveRange000
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 0 ≤ r.val) (hu : r.val < 50)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 ∨ r = 32 ∨ r = 33 ∨ r = 34 ∨ r = 35 ∨ r = 36 ∨ r = 37 ∨ r = 38 ∨ r = 39 ∨ r = 40 ∨ r = 41 ∨ r = 42 ∨ r = 43 ∨ r = 44 ∨ r = 45 ∨ r = 46 ∨ r = 47 ∨ r = 48 ∨ r = 49 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow000.row a ha
  · exact ColeskiPositiveRow001.row a ha
  · exact ColeskiPositiveRow002.row a ha
  · exact ColeskiPositiveRow003.row a ha
  · exact ColeskiPositiveRow004.row a ha
  · exact ColeskiPositiveRow005.row a ha
  · exact ColeskiPositiveRow006.row a ha
  · exact ColeskiPositiveRow007.row a ha
  · exact ColeskiPositiveRow008.row a ha
  · exact ColeskiPositiveRow009.row a ha
  · exact ColeskiPositiveRow010.row a ha
  · exact ColeskiPositiveRow011.row a ha
  · exact ColeskiPositiveRow012.row a ha
  · exact ColeskiPositiveRow013.row a ha
  · exact ColeskiPositiveRow014.row a ha
  · exact ColeskiPositiveRow015.row a ha
  · exact ColeskiPositiveRow016.row a ha
  · exact ColeskiPositiveRow017.row a ha
  · exact ColeskiPositiveRow018.row a ha
  · exact ColeskiPositiveRow019.row a ha
  · exact ColeskiPositiveRow020.row a ha
  · exact ColeskiPositiveRow021.row a ha
  · exact ColeskiPositiveRow022.row a ha
  · exact ColeskiPositiveRow023.row a ha
  · exact ColeskiPositiveRow024.row a ha
  · exact ColeskiPositiveRow025.row a ha
  · exact ColeskiPositiveRow026.row a ha
  · exact ColeskiPositiveRow027.row a ha
  · exact ColeskiPositiveRow028.row a ha
  · exact ColeskiPositiveRow029.row a ha
  · exact ColeskiPositiveRow030.row a ha
  · exact ColeskiPositiveRow031.row a ha
  · exact ColeskiPositiveRow032.row a ha
  · exact ColeskiPositiveRow033.row a ha
  · exact ColeskiPositiveRow034.row a ha
  · exact ColeskiPositiveRow035.row a ha
  · exact ColeskiPositiveRow036.row a ha
  · exact ColeskiPositiveRow037.row a ha
  · exact ColeskiPositiveRow038.row a ha
  · exact ColeskiPositiveRow039.row a ha
  · exact ColeskiPositiveRow040.row a ha
  · exact ColeskiPositiveRow041.row a ha
  · exact ColeskiPositiveRow042.row a ha
  · exact ColeskiPositiveRow043.row a ha
  · exact ColeskiPositiveRow044.row a ha
  · exact ColeskiPositiveRow045.row a ha
  · exact ColeskiPositiveRow046.row a ha
  · exact ColeskiPositiveRow047.row a ha
  · exact ColeskiPositiveRow048.row a ha
  · exact ColeskiPositiveRow049.row a ha
end ColeskiPositiveRange000
#print axioms ColeskiPositiveRange000.rows

/- END bundled local module PositiveRange000 -/

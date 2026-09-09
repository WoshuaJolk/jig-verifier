import Commons.ColeskiE811Sig20260909_PositiveRowsGroup050
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup055
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup060
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup065
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup070
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup075
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup080
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup085
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup090
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup095

/- BEGIN bundled local module PositiveRange050 -/

namespace ColeskiPositiveRange050
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 50 ≤ r.val) (hu : r.val < 100)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 50 ∨ r = 51 ∨ r = 52 ∨ r = 53 ∨ r = 54 ∨ r = 55 ∨ r = 56 ∨ r = 57 ∨ r = 58 ∨ r = 59 ∨ r = 60 ∨ r = 61 ∨ r = 62 ∨ r = 63 ∨ r = 64 ∨ r = 65 ∨ r = 66 ∨ r = 67 ∨ r = 68 ∨ r = 69 ∨ r = 70 ∨ r = 71 ∨ r = 72 ∨ r = 73 ∨ r = 74 ∨ r = 75 ∨ r = 76 ∨ r = 77 ∨ r = 78 ∨ r = 79 ∨ r = 80 ∨ r = 81 ∨ r = 82 ∨ r = 83 ∨ r = 84 ∨ r = 85 ∨ r = 86 ∨ r = 87 ∨ r = 88 ∨ r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 93 ∨ r = 94 ∨ r = 95 ∨ r = 96 ∨ r = 97 ∨ r = 98 ∨ r = 99 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow050.row a ha
  · exact ColeskiPositiveRow051.row a ha
  · exact ColeskiPositiveRow052.row a ha
  · exact ColeskiPositiveRow053.row a ha
  · exact ColeskiPositiveRow054.row a ha
  · exact ColeskiPositiveRow055.row a ha
  · exact ColeskiPositiveRow056.row a ha
  · exact ColeskiPositiveRow057.row a ha
  · exact ColeskiPositiveRow058.row a ha
  · exact ColeskiPositiveRow059.row a ha
  · exact ColeskiPositiveRow060.row a ha
  · exact ColeskiPositiveRow061.row a ha
  · exact ColeskiPositiveRow062.row a ha
  · exact ColeskiPositiveRow063.row a ha
  · exact ColeskiPositiveRow064.row a ha
  · exact ColeskiPositiveRow065.row a ha
  · exact ColeskiPositiveRow066.row a ha
  · exact ColeskiPositiveRow067.row a ha
  · exact ColeskiPositiveRow068.row a ha
  · exact ColeskiPositiveRow069.row a ha
  · exact ColeskiPositiveRow070.row a ha
  · exact ColeskiPositiveRow071.row a ha
  · exact ColeskiPositiveRow072.row a ha
  · exact ColeskiPositiveRow073.row a ha
  · exact ColeskiPositiveRow074.row a ha
  · exact ColeskiPositiveRow075.row a ha
  · exact ColeskiPositiveRow076.row a ha
  · exact ColeskiPositiveRow077.row a ha
  · exact ColeskiPositiveRow078.row a ha
  · exact ColeskiPositiveRow079.row a ha
  · exact ColeskiPositiveRow080.row a ha
  · exact ColeskiPositiveRow081.row a ha
  · exact ColeskiPositiveRow082.row a ha
  · exact ColeskiPositiveRow083.row a ha
  · exact ColeskiPositiveRow084.row a ha
  · exact ColeskiPositiveRow085.row a ha
  · exact ColeskiPositiveRow086.row a ha
  · exact ColeskiPositiveRow087.row a ha
  · exact ColeskiPositiveRow088.row a ha
  · exact ColeskiPositiveRow089.row a ha
  · exact ColeskiPositiveRow090.row a ha
  · exact ColeskiPositiveRow091.row a ha
  · exact ColeskiPositiveRow092.row a ha
  · exact ColeskiPositiveRow093.row a ha
  · exact ColeskiPositiveRow094.row a ha
  · exact ColeskiPositiveRow095.row a ha
  · exact ColeskiPositiveRow096.row a ha
  · exact ColeskiPositiveRow097.row a ha
  · exact ColeskiPositiveRow098.row a ha
  · exact ColeskiPositiveRow099.row a ha
end ColeskiPositiveRange050
#print axioms ColeskiPositiveRange050.rows

/- END bundled local module PositiveRange050 -/

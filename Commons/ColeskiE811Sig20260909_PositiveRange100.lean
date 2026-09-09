import Commons.ColeskiE811Sig20260909_PositiveRowsGroup100
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup105
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup110
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup115
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup120
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup125
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup130
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup135
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup140
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup145

/- BEGIN bundled local module PositiveRange100 -/

namespace ColeskiPositiveRange100
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 100 ≤ r.val) (hu : r.val < 150)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 100 ∨ r = 101 ∨ r = 102 ∨ r = 103 ∨ r = 104 ∨ r = 105 ∨ r = 106 ∨ r = 107 ∨ r = 108 ∨ r = 109 ∨ r = 110 ∨ r = 111 ∨ r = 112 ∨ r = 113 ∨ r = 114 ∨ r = 115 ∨ r = 116 ∨ r = 117 ∨ r = 118 ∨ r = 119 ∨ r = 120 ∨ r = 121 ∨ r = 122 ∨ r = 123 ∨ r = 124 ∨ r = 125 ∨ r = 126 ∨ r = 127 ∨ r = 128 ∨ r = 129 ∨ r = 130 ∨ r = 131 ∨ r = 132 ∨ r = 133 ∨ r = 134 ∨ r = 135 ∨ r = 136 ∨ r = 137 ∨ r = 138 ∨ r = 139 ∨ r = 140 ∨ r = 141 ∨ r = 142 ∨ r = 143 ∨ r = 144 ∨ r = 145 ∨ r = 146 ∨ r = 147 ∨ r = 148 ∨ r = 149 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow100.row a ha
  · exact ColeskiPositiveRow101.row a ha
  · exact ColeskiPositiveRow102.row a ha
  · exact ColeskiPositiveRow103.row a ha
  · exact ColeskiPositiveRow104.row a ha
  · exact ColeskiPositiveRow105.row a ha
  · exact ColeskiPositiveRow106.row a ha
  · exact ColeskiPositiveRow107.row a ha
  · exact ColeskiPositiveRow108.row a ha
  · exact ColeskiPositiveRow109.row a ha
  · exact ColeskiPositiveRow110.row a ha
  · exact ColeskiPositiveRow111.row a ha
  · exact ColeskiPositiveRow112.row a ha
  · exact ColeskiPositiveRow113.row a ha
  · exact ColeskiPositiveRow114.row a ha
  · exact ColeskiPositiveRow115.row a ha
  · exact ColeskiPositiveRow116.row a ha
  · exact ColeskiPositiveRow117.row a ha
  · exact ColeskiPositiveRow118.row a ha
  · exact ColeskiPositiveRow119.row a ha
  · exact ColeskiPositiveRow120.row a ha
  · exact ColeskiPositiveRow121.row a ha
  · exact ColeskiPositiveRow122.row a ha
  · exact ColeskiPositiveRow123.row a ha
  · exact ColeskiPositiveRow124.row a ha
  · exact ColeskiPositiveRow125.row a ha
  · exact ColeskiPositiveRow126.row a ha
  · exact ColeskiPositiveRow127.row a ha
  · exact ColeskiPositiveRow128.row a ha
  · exact ColeskiPositiveRow129.row a ha
  · exact ColeskiPositiveRow130.row a ha
  · exact ColeskiPositiveRow131.row a ha
  · exact ColeskiPositiveRow132.row a ha
  · exact ColeskiPositiveRow133.row a ha
  · exact ColeskiPositiveRow134.row a ha
  · exact ColeskiPositiveRow135.row a ha
  · exact ColeskiPositiveRow136.row a ha
  · exact ColeskiPositiveRow137.row a ha
  · exact ColeskiPositiveRow138.row a ha
  · exact ColeskiPositiveRow139.row a ha
  · exact ColeskiPositiveRow140.row a ha
  · exact ColeskiPositiveRow141.row a ha
  · exact ColeskiPositiveRow142.row a ha
  · exact ColeskiPositiveRow143.row a ha
  · exact ColeskiPositiveRow144.row a ha
  · exact ColeskiPositiveRow145.row a ha
  · exact ColeskiPositiveRow146.row a ha
  · exact ColeskiPositiveRow147.row a ha
  · exact ColeskiPositiveRow148.row a ha
  · exact ColeskiPositiveRow149.row a ha
end ColeskiPositiveRange100
#print axioms ColeskiPositiveRange100.rows

/- END bundled local module PositiveRange100 -/

import Commons.ColeskiE811Sig20260909_PositiveRowsGroup150
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup155
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup160
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup165
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup170
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup175
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup180
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup185
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup190
import Commons.ColeskiE811Sig20260909_PositiveRowsGroup195

/- BEGIN bundled local module PositiveRange150 -/

namespace ColeskiPositiveRange150
open ColeskiK5Coverage ColeskiSixAllowed ColeskiK6Check
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hl : 150 ≤ r.val) (hu : r.val < 200)
    (a : Fin 7776) (ha : allowedExtension6 representatives5[r.val]! a.val = true) :
    ∃ ws : Array Nat, checkPositive representatives5[r.val]! a.val ws = true := by
  have hr : r = 150 ∨ r = 151 ∨ r = 152 ∨ r = 153 ∨ r = 154 ∨ r = 155 ∨ r = 156 ∨ r = 157 ∨ r = 158 ∨ r = 159 ∨ r = 160 ∨ r = 161 ∨ r = 162 ∨ r = 163 ∨ r = 164 ∨ r = 165 ∨ r = 166 ∨ r = 167 ∨ r = 168 ∨ r = 169 ∨ r = 170 ∨ r = 171 ∨ r = 172 ∨ r = 173 ∨ r = 174 ∨ r = 175 ∨ r = 176 ∨ r = 177 ∨ r = 178 ∨ r = 179 ∨ r = 180 ∨ r = 181 ∨ r = 182 ∨ r = 183 ∨ r = 184 ∨ r = 185 ∨ r = 186 ∨ r = 187 ∨ r = 188 ∨ r = 189 ∨ r = 190 ∨ r = 191 ∨ r = 192 ∨ r = 193 ∨ r = 194 ∨ r = 195 ∨ r = 196 ∨ r = 197 ∨ r = 198 ∨ r = 199 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiPositiveRow150.row a ha
  · exact ColeskiPositiveRow151.row a ha
  · exact ColeskiPositiveRow152.row a ha
  · exact ColeskiPositiveRow153.row a ha
  · exact ColeskiPositiveRow154.row a ha
  · exact ColeskiPositiveRow155.row a ha
  · exact ColeskiPositiveRow156.row a ha
  · exact ColeskiPositiveRow157.row a ha
  · exact ColeskiPositiveRow158.row a ha
  · exact ColeskiPositiveRow159.row a ha
  · exact ColeskiPositiveRow160.row a ha
  · exact ColeskiPositiveRow161.row a ha
  · exact ColeskiPositiveRow162.row a ha
  · exact ColeskiPositiveRow163.row a ha
  · exact ColeskiPositiveRow164.row a ha
  · exact ColeskiPositiveRow165.row a ha
  · exact ColeskiPositiveRow166.row a ha
  · exact ColeskiPositiveRow167.row a ha
  · exact ColeskiPositiveRow168.row a ha
  · exact ColeskiPositiveRow169.row a ha
  · exact ColeskiPositiveRow170.row a ha
  · exact ColeskiPositiveRow171.row a ha
  · exact ColeskiPositiveRow172.row a ha
  · exact ColeskiPositiveRow173.row a ha
  · exact ColeskiPositiveRow174.row a ha
  · exact ColeskiPositiveRow175.row a ha
  · exact ColeskiPositiveRow176.row a ha
  · exact ColeskiPositiveRow177.row a ha
  · exact ColeskiPositiveRow178.row a ha
  · exact ColeskiPositiveRow179.row a ha
  · exact ColeskiPositiveRow180.row a ha
  · exact ColeskiPositiveRow181.row a ha
  · exact ColeskiPositiveRow182.row a ha
  · exact ColeskiPositiveRow183.row a ha
  · exact ColeskiPositiveRow184.row a ha
  · exact ColeskiPositiveRow185.row a ha
  · exact ColeskiPositiveRow186.row a ha
  · exact ColeskiPositiveRow187.row a ha
  · exact ColeskiPositiveRow188.row a ha
  · exact ColeskiPositiveRow189.row a ha
  · exact ColeskiPositiveRow190.row a ha
  · exact ColeskiPositiveRow191.row a ha
  · exact ColeskiPositiveRow192.row a ha
  · exact ColeskiPositiveRow193.row a ha
  · exact ColeskiPositiveRow194.row a ha
  · exact ColeskiPositiveRow195.row a ha
  · exact ColeskiPositiveRow196.row a ha
  · exact ColeskiPositiveRow197.row a ha
  · exact ColeskiPositiveRow198.row a ha
  · exact ColeskiPositiveRow199.row a ha
end ColeskiPositiveRange150
#print axioms ColeskiPositiveRange150.rows

/- END bundled local module PositiveRange150 -/

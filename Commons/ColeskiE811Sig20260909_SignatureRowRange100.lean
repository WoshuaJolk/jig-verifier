import Commons.ColeskiE811Sig20260909_SignatureRows100
import Commons.ColeskiE811Sig20260909_SignatureRows105
import Commons.ColeskiE811Sig20260909_SignatureRows110
import Commons.ColeskiE811Sig20260909_SignatureRows115
import Commons.ColeskiE811Sig20260909_SignatureRows120
import Commons.ColeskiE811Sig20260909_SignatureRows125
import Commons.ColeskiE811Sig20260909_SignatureRows130
import Commons.ColeskiE811Sig20260909_SignatureRows135
import Commons.ColeskiE811Sig20260909_SignatureRows140
import Commons.ColeskiE811Sig20260909_SignatureRows145

/- BEGIN bundled local module SignatureRowRange100 -/


namespace ColeskiSignatureRowRange100

open ColeskiSignatureRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows (r : Fin 551) (hlo : 100 ≤ r.val) (hhi : r.val < 150) : rowMatches r := by
  have hr : r = 100 ∨ r = 101 ∨ r = 102 ∨ r = 103 ∨ r = 104 ∨ r = 105 ∨ r = 106 ∨ r = 107 ∨ r = 108 ∨ r = 109 ∨ r = 110 ∨ r = 111 ∨ r = 112 ∨ r = 113 ∨ r = 114 ∨ r = 115 ∨ r = 116 ∨ r = 117 ∨ r = 118 ∨ r = 119 ∨ r = 120 ∨ r = 121 ∨ r = 122 ∨ r = 123 ∨ r = 124 ∨ r = 125 ∨ r = 126 ∨ r = 127 ∨ r = 128 ∨ r = 129 ∨ r = 130 ∨ r = 131 ∨ r = 132 ∨ r = 133 ∨ r = 134 ∨ r = 135 ∨ r = 136 ∨ r = 137 ∨ r = 138 ∨ r = 139 ∨ r = 140 ∨ r = 141 ∨ r = 142 ∨ r = 143 ∨ r = 144 ∨ r = 145 ∨ r = 146 ∨ r = 147 ∨ r = 148 ∨ r = 149 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ColeskiSignatureRows.Block100.row100
  · exact ColeskiSignatureRows.Block100.row101
  · exact ColeskiSignatureRows.Block100.row102
  · exact ColeskiSignatureRows.Block100.row103
  · exact ColeskiSignatureRows.Block100.row104
  · exact ColeskiSignatureRows.Block105.row105
  · exact ColeskiSignatureRows.Block105.row106
  · exact ColeskiSignatureRows.Block105.row107
  · exact ColeskiSignatureRows.Block105.row108
  · exact ColeskiSignatureRows.Block105.row109
  · exact ColeskiSignatureRows.Block110.row110
  · exact ColeskiSignatureRows.Block110.row111
  · exact ColeskiSignatureRows.Block110.row112
  · exact ColeskiSignatureRows.Block110.row113
  · exact ColeskiSignatureRows.Block110.row114
  · exact ColeskiSignatureRows.Block115.row115
  · exact ColeskiSignatureRows.Block115.row116
  · exact ColeskiSignatureRows.Block115.row117
  · exact ColeskiSignatureRows.Block115.row118
  · exact ColeskiSignatureRows.Block115.row119
  · exact ColeskiSignatureRows.Block120.row120
  · exact ColeskiSignatureRows.Block120.row121
  · exact ColeskiSignatureRows.Block120.row122
  · exact ColeskiSignatureRows.Block120.row123
  · exact ColeskiSignatureRows.Block120.row124
  · exact ColeskiSignatureRows.Block125.row125
  · exact ColeskiSignatureRows.Block125.row126
  · exact ColeskiSignatureRows.Block125.row127
  · exact ColeskiSignatureRows.Block125.row128
  · exact ColeskiSignatureRows.Block125.row129
  · exact ColeskiSignatureRows.Block130.row130
  · exact ColeskiSignatureRows.Block130.row131
  · exact ColeskiSignatureRows.Block130.row132
  · exact ColeskiSignatureRows.Block130.row133
  · exact ColeskiSignatureRows.Block130.row134
  · exact ColeskiSignatureRows.Block135.row135
  · exact ColeskiSignatureRows.Block135.row136
  · exact ColeskiSignatureRows.Block135.row137
  · exact ColeskiSignatureRows.Block135.row138
  · exact ColeskiSignatureRows.Block135.row139
  · exact ColeskiSignatureRows.Block140.row140
  · exact ColeskiSignatureRows.Block140.row141
  · exact ColeskiSignatureRows.Block140.row142
  · exact ColeskiSignatureRows.Block140.row143
  · exact ColeskiSignatureRows.Block140.row144
  · exact ColeskiSignatureRows.Block145.row145
  · exact ColeskiSignatureRows.Block145.row146
  · exact ColeskiSignatureRows.Block145.row147
  · exact ColeskiSignatureRows.Block145.row148
  · exact ColeskiSignatureRows.Block145.row149

end ColeskiSignatureRowRange100

/- END bundled local module SignatureRowRange100 -/

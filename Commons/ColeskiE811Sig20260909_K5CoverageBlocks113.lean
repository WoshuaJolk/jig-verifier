import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks113 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock113 : ((List.range 256).all fun k => check5 (113*256+k)) = true := by decide
theorem extraBlock114 : ((List.range 256).all fun k => check5 (114*256+k)) = true := by decide
theorem extraBlock115 : ((List.range 256).all fun k => check5 (115*256+k)) = true := by decide
theorem extraBlock116 : ((List.range 256).all fun k => check5 (116*256+k)) = true := by decide
theorem extraBlock117 : ((List.range 256).all fun k => check5 (117*256+k)) = true := by decide
theorem extraBlock118 : ((List.range 256).all fun k => check5 (118*256+k)) = true := by decide
theorem extraBlock119 : ((List.range 256).all fun k => check5 (119*256+k)) = true := by decide
theorem extraBlock120 : ((List.range 256).all fun k => check5 (120*256+k)) = true := by decide
theorem extraBlock121 : ((List.range 256).all fun k => check5 (121*256+k)) = true := by decide
theorem extraBlock122 : ((List.range 256).all fun k => check5 (122*256+k)) = true := by decide
theorem extraBlock123 : ((List.range 256).all fun k => check5 (123*256+k)) = true := by decide
theorem extraBlock124 : ((List.range 256).all fun k => check5 (124*256+k)) = true := by decide
theorem extraBlock125 : ((List.range 256).all fun k => check5 (125*256+k)) = true := by decide
theorem extraBlock126 : ((List.range 144).all fun k => check5 (126*256+k)) = true := by decide
theorem group113 (i : Fin 14) :
    ((List.range (if 113+i.val = 126 then 144 else 256)).all
      fun k => check5 ((113+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock113
  · exact extraBlock114
  · exact extraBlock115
  · exact extraBlock116
  · exact extraBlock117
  · exact extraBlock118
  · exact extraBlock119
  · exact extraBlock120
  · exact extraBlock121
  · exact extraBlock122
  · exact extraBlock123
  · exact extraBlock124
  · exact extraBlock125
  · exact extraBlock126

theorem group113_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 113 + i.val = 126 then 144 else 256) :
    check5 ((113 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group113 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks113 -/

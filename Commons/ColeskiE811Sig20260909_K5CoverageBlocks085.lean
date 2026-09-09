import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks085 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock85 : ((List.range 256).all fun k => check5 (85*256+k)) = true := by decide
theorem extraBlock86 : ((List.range 256).all fun k => check5 (86*256+k)) = true := by decide
theorem extraBlock87 : ((List.range 256).all fun k => check5 (87*256+k)) = true := by decide
theorem extraBlock88 : ((List.range 256).all fun k => check5 (88*256+k)) = true := by decide
theorem extraBlock89 : ((List.range 256).all fun k => check5 (89*256+k)) = true := by decide
theorem extraBlock90 : ((List.range 256).all fun k => check5 (90*256+k)) = true := by decide
theorem extraBlock91 : ((List.range 256).all fun k => check5 (91*256+k)) = true := by decide
theorem extraBlock92 : ((List.range 256).all fun k => check5 (92*256+k)) = true := by decide
theorem extraBlock93 : ((List.range 256).all fun k => check5 (93*256+k)) = true := by decide
theorem extraBlock94 : ((List.range 256).all fun k => check5 (94*256+k)) = true := by decide
theorem extraBlock95 : ((List.range 256).all fun k => check5 (95*256+k)) = true := by decide
theorem extraBlock96 : ((List.range 256).all fun k => check5 (96*256+k)) = true := by decide
theorem extraBlock97 : ((List.range 256).all fun k => check5 (97*256+k)) = true := by decide
theorem extraBlock98 : ((List.range 256).all fun k => check5 (98*256+k)) = true := by decide
theorem group085 (i : Fin 14) :
    ((List.range (if 85+i.val = 126 then 144 else 256)).all
      fun k => check5 ((85+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock85
  · exact extraBlock86
  · exact extraBlock87
  · exact extraBlock88
  · exact extraBlock89
  · exact extraBlock90
  · exact extraBlock91
  · exact extraBlock92
  · exact extraBlock93
  · exact extraBlock94
  · exact extraBlock95
  · exact extraBlock96
  · exact extraBlock97
  · exact extraBlock98

theorem group085_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 85 + i.val = 126 then 144 else 256) :
    check5 ((85 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group085 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks085 -/

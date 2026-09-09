import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks099 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock99 : ((List.range 256).all fun k => check5 (99*256+k)) = true := by decide
theorem extraBlock100 : ((List.range 256).all fun k => check5 (100*256+k)) = true := by decide
theorem extraBlock101 : ((List.range 256).all fun k => check5 (101*256+k)) = true := by decide
theorem extraBlock102 : ((List.range 256).all fun k => check5 (102*256+k)) = true := by decide
theorem extraBlock103 : ((List.range 256).all fun k => check5 (103*256+k)) = true := by decide
theorem extraBlock104 : ((List.range 256).all fun k => check5 (104*256+k)) = true := by decide
theorem extraBlock105 : ((List.range 256).all fun k => check5 (105*256+k)) = true := by decide
theorem extraBlock106 : ((List.range 256).all fun k => check5 (106*256+k)) = true := by decide
theorem extraBlock107 : ((List.range 256).all fun k => check5 (107*256+k)) = true := by decide
theorem extraBlock108 : ((List.range 256).all fun k => check5 (108*256+k)) = true := by decide
theorem extraBlock109 : ((List.range 256).all fun k => check5 (109*256+k)) = true := by decide
theorem extraBlock110 : ((List.range 256).all fun k => check5 (110*256+k)) = true := by decide
theorem extraBlock111 : ((List.range 256).all fun k => check5 (111*256+k)) = true := by decide
theorem extraBlock112 : ((List.range 256).all fun k => check5 (112*256+k)) = true := by decide
theorem group099 (i : Fin 14) :
    ((List.range (if 99+i.val = 126 then 144 else 256)).all
      fun k => check5 ((99+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock99
  · exact extraBlock100
  · exact extraBlock101
  · exact extraBlock102
  · exact extraBlock103
  · exact extraBlock104
  · exact extraBlock105
  · exact extraBlock106
  · exact extraBlock107
  · exact extraBlock108
  · exact extraBlock109
  · exact extraBlock110
  · exact extraBlock111
  · exact extraBlock112

theorem group099_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 99 + i.val = 126 then 144 else 256) :
    check5 ((99 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group099 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks099 -/

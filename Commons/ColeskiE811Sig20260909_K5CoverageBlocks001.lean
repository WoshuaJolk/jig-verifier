import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks001 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock1 : ((List.range 256).all fun k => check5 (1*256+k)) = true := by decide
theorem extraBlock2 : ((List.range 256).all fun k => check5 (2*256+k)) = true := by decide
theorem extraBlock3 : ((List.range 256).all fun k => check5 (3*256+k)) = true := by decide
theorem extraBlock4 : ((List.range 256).all fun k => check5 (4*256+k)) = true := by decide
theorem extraBlock5 : ((List.range 256).all fun k => check5 (5*256+k)) = true := by decide
theorem extraBlock6 : ((List.range 256).all fun k => check5 (6*256+k)) = true := by decide
theorem extraBlock7 : ((List.range 256).all fun k => check5 (7*256+k)) = true := by decide
theorem extraBlock8 : ((List.range 256).all fun k => check5 (8*256+k)) = true := by decide
theorem extraBlock9 : ((List.range 256).all fun k => check5 (9*256+k)) = true := by decide
theorem extraBlock10 : ((List.range 256).all fun k => check5 (10*256+k)) = true := by decide
theorem extraBlock11 : ((List.range 256).all fun k => check5 (11*256+k)) = true := by decide
theorem extraBlock12 : ((List.range 256).all fun k => check5 (12*256+k)) = true := by decide
theorem extraBlock13 : ((List.range 256).all fun k => check5 (13*256+k)) = true := by decide
theorem extraBlock14 : ((List.range 256).all fun k => check5 (14*256+k)) = true := by decide
theorem group001 (i : Fin 14) :
    ((List.range (if 1+i.val = 126 then 144 else 256)).all
      fun k => check5 ((1+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock1
  · exact extraBlock2
  · exact extraBlock3
  · exact extraBlock4
  · exact extraBlock5
  · exact extraBlock6
  · exact extraBlock7
  · exact extraBlock8
  · exact extraBlock9
  · exact extraBlock10
  · exact extraBlock11
  · exact extraBlock12
  · exact extraBlock13
  · exact extraBlock14

theorem group001_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 1 + i.val = 126 then 144 else 256) :
    check5 ((1 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group001 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks001 -/

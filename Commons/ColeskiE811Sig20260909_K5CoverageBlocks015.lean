import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks015 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock15 : ((List.range 256).all fun k => check5 (15*256+k)) = true := by decide
theorem extraBlock16 : ((List.range 256).all fun k => check5 (16*256+k)) = true := by decide
theorem extraBlock17 : ((List.range 256).all fun k => check5 (17*256+k)) = true := by decide
theorem extraBlock18 : ((List.range 256).all fun k => check5 (18*256+k)) = true := by decide
theorem extraBlock19 : ((List.range 256).all fun k => check5 (19*256+k)) = true := by decide
theorem extraBlock20 : ((List.range 256).all fun k => check5 (20*256+k)) = true := by decide
theorem extraBlock21 : ((List.range 256).all fun k => check5 (21*256+k)) = true := by decide
theorem extraBlock22 : ((List.range 256).all fun k => check5 (22*256+k)) = true := by decide
theorem extraBlock23 : ((List.range 256).all fun k => check5 (23*256+k)) = true := by decide
theorem extraBlock24 : ((List.range 256).all fun k => check5 (24*256+k)) = true := by decide
theorem extraBlock25 : ((List.range 256).all fun k => check5 (25*256+k)) = true := by decide
theorem extraBlock26 : ((List.range 256).all fun k => check5 (26*256+k)) = true := by decide
theorem extraBlock27 : ((List.range 256).all fun k => check5 (27*256+k)) = true := by decide
theorem extraBlock28 : ((List.range 256).all fun k => check5 (28*256+k)) = true := by decide
theorem group015 (i : Fin 14) :
    ((List.range (if 15+i.val = 126 then 144 else 256)).all
      fun k => check5 ((15+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock15
  · exact extraBlock16
  · exact extraBlock17
  · exact extraBlock18
  · exact extraBlock19
  · exact extraBlock20
  · exact extraBlock21
  · exact extraBlock22
  · exact extraBlock23
  · exact extraBlock24
  · exact extraBlock25
  · exact extraBlock26
  · exact extraBlock27
  · exact extraBlock28

theorem group015_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 15 + i.val = 126 then 144 else 256) :
    check5 ((15 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group015 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks015 -/

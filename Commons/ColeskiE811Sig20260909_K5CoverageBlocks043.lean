import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks043 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock43 : ((List.range 256).all fun k => check5 (43*256+k)) = true := by decide
theorem extraBlock44 : ((List.range 256).all fun k => check5 (44*256+k)) = true := by decide
theorem extraBlock45 : ((List.range 256).all fun k => check5 (45*256+k)) = true := by decide
theorem extraBlock46 : ((List.range 256).all fun k => check5 (46*256+k)) = true := by decide
theorem extraBlock47 : ((List.range 256).all fun k => check5 (47*256+k)) = true := by decide
theorem extraBlock48 : ((List.range 256).all fun k => check5 (48*256+k)) = true := by decide
theorem extraBlock49 : ((List.range 256).all fun k => check5 (49*256+k)) = true := by decide
theorem extraBlock50 : ((List.range 256).all fun k => check5 (50*256+k)) = true := by decide
theorem extraBlock51 : ((List.range 256).all fun k => check5 (51*256+k)) = true := by decide
theorem extraBlock52 : ((List.range 256).all fun k => check5 (52*256+k)) = true := by decide
theorem extraBlock53 : ((List.range 256).all fun k => check5 (53*256+k)) = true := by decide
theorem extraBlock54 : ((List.range 256).all fun k => check5 (54*256+k)) = true := by decide
theorem extraBlock55 : ((List.range 256).all fun k => check5 (55*256+k)) = true := by decide
theorem extraBlock56 : ((List.range 256).all fun k => check5 (56*256+k)) = true := by decide
theorem group043 (i : Fin 14) :
    ((List.range (if 43+i.val = 126 then 144 else 256)).all
      fun k => check5 ((43+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock43
  · exact extraBlock44
  · exact extraBlock45
  · exact extraBlock46
  · exact extraBlock47
  · exact extraBlock48
  · exact extraBlock49
  · exact extraBlock50
  · exact extraBlock51
  · exact extraBlock52
  · exact extraBlock53
  · exact extraBlock54
  · exact extraBlock55
  · exact extraBlock56

theorem group043_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 43 + i.val = 126 then 144 else 256) :
    check5 ((43 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group043 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks043 -/

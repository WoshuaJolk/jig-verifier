import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks057 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock57 : ((List.range 256).all fun k => check5 (57*256+k)) = true := by decide
theorem extraBlock58 : ((List.range 256).all fun k => check5 (58*256+k)) = true := by decide
theorem extraBlock59 : ((List.range 256).all fun k => check5 (59*256+k)) = true := by decide
theorem extraBlock60 : ((List.range 256).all fun k => check5 (60*256+k)) = true := by decide
theorem extraBlock61 : ((List.range 256).all fun k => check5 (61*256+k)) = true := by decide
theorem extraBlock62 : ((List.range 256).all fun k => check5 (62*256+k)) = true := by decide
theorem extraBlock63 : ((List.range 256).all fun k => check5 (63*256+k)) = true := by decide
theorem extraBlock64 : ((List.range 256).all fun k => check5 (64*256+k)) = true := by decide
theorem extraBlock65 : ((List.range 256).all fun k => check5 (65*256+k)) = true := by decide
theorem extraBlock66 : ((List.range 256).all fun k => check5 (66*256+k)) = true := by decide
theorem extraBlock67 : ((List.range 256).all fun k => check5 (67*256+k)) = true := by decide
theorem extraBlock68 : ((List.range 256).all fun k => check5 (68*256+k)) = true := by decide
theorem extraBlock69 : ((List.range 256).all fun k => check5 (69*256+k)) = true := by decide
theorem extraBlock70 : ((List.range 256).all fun k => check5 (70*256+k)) = true := by decide
theorem group057 (i : Fin 14) :
    ((List.range (if 57+i.val = 126 then 144 else 256)).all
      fun k => check5 ((57+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock57
  · exact extraBlock58
  · exact extraBlock59
  · exact extraBlock60
  · exact extraBlock61
  · exact extraBlock62
  · exact extraBlock63
  · exact extraBlock64
  · exact extraBlock65
  · exact extraBlock66
  · exact extraBlock67
  · exact extraBlock68
  · exact extraBlock69
  · exact extraBlock70

theorem group057_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 57 + i.val = 126 then 144 else 256) :
    check5 ((57 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group057 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks057 -/

import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks071 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock71 : ((List.range 256).all fun k => check5 (71*256+k)) = true := by decide
theorem extraBlock72 : ((List.range 256).all fun k => check5 (72*256+k)) = true := by decide
theorem extraBlock73 : ((List.range 256).all fun k => check5 (73*256+k)) = true := by decide
theorem extraBlock74 : ((List.range 256).all fun k => check5 (74*256+k)) = true := by decide
theorem extraBlock75 : ((List.range 256).all fun k => check5 (75*256+k)) = true := by decide
theorem extraBlock76 : ((List.range 256).all fun k => check5 (76*256+k)) = true := by decide
theorem extraBlock77 : ((List.range 256).all fun k => check5 (77*256+k)) = true := by decide
theorem extraBlock78 : ((List.range 256).all fun k => check5 (78*256+k)) = true := by decide
theorem extraBlock79 : ((List.range 256).all fun k => check5 (79*256+k)) = true := by decide
theorem extraBlock80 : ((List.range 256).all fun k => check5 (80*256+k)) = true := by decide
theorem extraBlock81 : ((List.range 256).all fun k => check5 (81*256+k)) = true := by decide
theorem extraBlock82 : ((List.range 256).all fun k => check5 (82*256+k)) = true := by decide
theorem extraBlock83 : ((List.range 256).all fun k => check5 (83*256+k)) = true := by decide
theorem extraBlock84 : ((List.range 256).all fun k => check5 (84*256+k)) = true := by decide
theorem group071 (i : Fin 14) :
    ((List.range (if 71+i.val = 126 then 144 else 256)).all
      fun k => check5 ((71+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock71
  · exact extraBlock72
  · exact extraBlock73
  · exact extraBlock74
  · exact extraBlock75
  · exact extraBlock76
  · exact extraBlock77
  · exact extraBlock78
  · exact extraBlock79
  · exact extraBlock80
  · exact extraBlock81
  · exact extraBlock82
  · exact extraBlock83
  · exact extraBlock84

theorem group071_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 71 + i.val = 126 then 144 else 256) :
    check5 ((71 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group071 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks071 -/

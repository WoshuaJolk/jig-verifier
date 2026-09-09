import Commons.ColeskiE811Sig20260909_K5Coverage

/- BEGIN bundled local module K5CoverageBlocks029 -/

namespace ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem extraBlock29 : ((List.range 256).all fun k => check5 (29*256+k)) = true := by decide
theorem extraBlock30 : ((List.range 256).all fun k => check5 (30*256+k)) = true := by decide
theorem extraBlock31 : ((List.range 256).all fun k => check5 (31*256+k)) = true := by decide
theorem extraBlock32 : ((List.range 256).all fun k => check5 (32*256+k)) = true := by decide
theorem extraBlock33 : ((List.range 256).all fun k => check5 (33*256+k)) = true := by decide
theorem extraBlock34 : ((List.range 256).all fun k => check5 (34*256+k)) = true := by decide
theorem extraBlock35 : ((List.range 256).all fun k => check5 (35*256+k)) = true := by decide
theorem extraBlock36 : ((List.range 256).all fun k => check5 (36*256+k)) = true := by decide
theorem extraBlock37 : ((List.range 256).all fun k => check5 (37*256+k)) = true := by decide
theorem extraBlock38 : ((List.range 256).all fun k => check5 (38*256+k)) = true := by decide
theorem extraBlock39 : ((List.range 256).all fun k => check5 (39*256+k)) = true := by decide
theorem extraBlock40 : ((List.range 256).all fun k => check5 (40*256+k)) = true := by decide
theorem extraBlock41 : ((List.range 256).all fun k => check5 (41*256+k)) = true := by decide
theorem extraBlock42 : ((List.range 256).all fun k => check5 (42*256+k)) = true := by decide
theorem group029 (i : Fin 14) :
    ((List.range (if 29+i.val = 126 then 144 else 256)).all
      fun k => check5 ((29+i.val)*256+k)) = true := by
  fin_cases i
  · exact extraBlock29
  · exact extraBlock30
  · exact extraBlock31
  · exact extraBlock32
  · exact extraBlock33
  · exact extraBlock34
  · exact extraBlock35
  · exact extraBlock36
  · exact extraBlock37
  · exact extraBlock38
  · exact extraBlock39
  · exact extraBlock40
  · exact extraBlock41
  · exact extraBlock42

theorem group029_pointwise (i : Fin 14) (k : Nat)
    (hk : k < if 29 + i.val = 126 then 144 else 256) :
    check5 ((29 + i.val) * 256 + k) = true := by
  apply List.all_eq_true.mp (group029 i)
  simpa only [List.mem_range] using hk
end ColeskiK5Coverage

/- END bundled local module K5CoverageBlocks029 -/

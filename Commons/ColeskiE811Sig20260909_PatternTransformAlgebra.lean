import Commons.ColeskiE811Sig20260909_PatternTransformEdge

/- BEGIN bundled local module PatternTransformAlgebra -/

namespace ColeskiPatternTransform
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar ColeskiTablePermutations
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem transformPattern_code (r : Nat) (v : Fin 120) (c : Fin 60) :
    patternCode (transformPattern r v c) =
    transformCode r edgeMaps5[v.val]! colorPermutations[c.val]! := by
  rw [transformCode_encode]
  simp only [patternCode, transformPattern_edge, Option.getD_some]
end ColeskiPatternTransform
#print axioms ColeskiPatternTransform.transformPattern_code

/- END bundled local module PatternTransformAlgebra -/

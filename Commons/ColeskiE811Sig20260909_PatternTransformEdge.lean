import Commons.ColeskiE811Sig20260909_PatternTransformNumeric

/- BEGIN bundled local module PatternTransformEdge -/


namespace ColeskiPatternTransform

open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar ColeskiTablePermutations

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def transformPattern (r : Nat) (v : Fin 120) (c : Fin 60) :=
  fun u w => (fromCode r (vertexPerm v u) (vertexPerm v w)).map (colorPerm c)

theorem transformPattern_edge (r : Nat) (v : Fin 120) (c : Fin 60) (e : Fin 10) :
    transformPattern r v c (edgeVertices e).1 (edgeVertices e).2 =
    some (numericEdge r edgeMaps5[v.val]! colorPermutations[c.val]! e) := by
  have h := table_edge_index v e
  have hn : vertexPerm v (edgeVertices e).1 ≠ vertexPerm v (edgeVertices e).2 := by
    intro he
    exact h.1 (congrArg Fin.val he)
  simp only [transformPattern, fromCode, if_neg hn, Option.map_some]
  apply congrArg some
  apply Fin.ext
  change digit colorPermutations[c.val]! (digit r (edgeIndex
    (min (digit vertexPermutations5[v.val]! (edgeVertices e).1.val)
      (digit vertexPermutations5[v.val]! (edgeVertices e).2.val))
    (max (digit vertexPermutations5[v.val]! (edgeVertices e).1.val)
      (digit vertexPermutations5[v.val]! (edgeVertices e).2.val)))) = _
  rw [h.2]
  rfl

end ColeskiPatternTransform

#print axioms ColeskiPatternTransform.transformPattern_edge

/- END bundled local module PatternTransformEdge -/

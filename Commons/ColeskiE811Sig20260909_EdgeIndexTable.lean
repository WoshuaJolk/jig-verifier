import Commons.ColeskiE811Sig20260909_PatternScalar
import Commons.ColeskiE811Sig20260909_TablePermutations

/- BEGIN bundled local module EdgeIndexTable -/

namespace ColeskiPatternTransform
open ColeskiK4Coverage ColeskiK5Coverage ColeskiPatternCode ColeskiPatternScalar ColeskiTablePermutations

theorem edge_roundtrip (k : Fin 10) : edgeLeft5 k < edgeRight5 k ∧
    edgeIndex (edgeLeft5 k) (edgeRight5 k) = k.val := by
  fin_cases k <;> decide

theorem edge_vertices_code (e : Fin 10) :
    (edgeVertices e).1.val = edgeLeft5 e ∧ (edgeVertices e).2.val = edgeRight5 e := by
  fin_cases e <;> decide

theorem table_edge_index : ∀ v : Fin 120, ∀ e : Fin 10,
    let a := digit vertexPermutations5[v.val]! (edgeVertices e).1.val
    let b := digit vertexPermutations5[v.val]! (edgeVertices e).2.val
    a ≠ b ∧ edgeIndex (min a b) (max a b) = edgeMaps5[v.val]!/10^e.val%10 := by
  intro v e
  dsimp only
  rw [(edge_vertices_code e).1, (edge_vertices_code e).2]
  have h := edge_maps5_induced v e
  dsimp only at h
  have hk : edgeMaps5[v.val]! / 10^e.val % 10 < 10 := Nat.mod_lt _ (by decide)
  have hr := edge_roundtrip ⟨_,hk⟩
  dsimp only at hr
  constructor
  · rw [h.1,h.2] at hr
    omega
  · rw [← h.1,← h.2]
    exact hr.2
end ColeskiPatternTransform
#print axioms ColeskiPatternTransform.table_edge_index

/- END bundled local module EdgeIndexTable -/

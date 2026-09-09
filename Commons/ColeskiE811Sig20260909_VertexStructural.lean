import Commons.ColeskiE811Sig20260909_TablePermutations

/- BEGIN bundled local module VertexStructural -/

namespace ColeskiVertexStructural
open ColeskiK4Coverage ColeskiK5Coverage ColeskiTablePermutations
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem vertex_tuple_table : ∀ a b c d e : Fin 5,
    [a,b,c,d,e].Nodup →
    ∃ i : Fin 120, digit vertexPermutations5[i.val]! 0 = a.val ∧
      digit vertexPermutations5[i.val]! 1 = b.val ∧
      digit vertexPermutations5[i.val]! 2 = c.val ∧
      digit vertexPermutations5[i.val]! 3 = d.val ∧
      digit vertexPermutations5[i.val]! 4 = e.val := by
  intro a
  fin_cases a <;> decide

theorem vertex_table_surjective (p : Equiv.Perm (Fin 5)) :
    ∃ i : Fin 120, p = vertexPerm i := by
  have h := vertex_tuple_table (p 0) (p 1) (p 2) (p 3) (p 4)
    (by simp [p.injective.eq_iff])
  obtain ⟨i,h0,h1,h2,h3,h4⟩ := h
  refine ⟨i,?_⟩
  apply Equiv.ext
  intro x
  fin_cases x
  · exact Fin.ext h0.symm
  · exact Fin.ext h1.symm
  · exact Fin.ext h2.symm
  · exact Fin.ext h3.symm
  · exact Fin.ext h4.symm
end ColeskiVertexStructural
#print axioms ColeskiVertexStructural.vertex_table_surjective

/- END bundled local module VertexStructural -/

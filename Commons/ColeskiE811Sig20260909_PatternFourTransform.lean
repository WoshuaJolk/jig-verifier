import Commons.ColeskiE811Sig20260909_PatternFour
import Commons.ColeskiE811Sig20260909_FourPermutation
import Commons.ColeskiE811Sig20260909_PaletteGroup
import Commons.ColeskiE811Sig20260909_PatternFaithfulness
import Commons.ColeskiE811Sig20260909_K4CoverageExtra

/- BEGIN bundled local module PatternFourTransform -/

namespace ColeskiPatternFourTransform
open ColeskiK4Coverage ColeskiPatternFour ColeskiFourPermutation ColeskiTablePermutations
open ColeskiPaletteAction ColeskiPatternAction ColeskiPatternFaithfulness
set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem edge_roundtrip (k : Fin 6) : edgeLeft k < edgeRight k ∧
    edgeIndex (edgeLeft k) (edgeRight k) = k.val := by fin_cases k <;> decide

theorem edge_vertices_code (e : Fin 6) :
    (edgeVertices e).1.val = edgeLeft e ∧ (edgeVertices e).2.val = edgeRight e := by
  fin_cases e <;> decide

theorem table_edge_index (v : Fin 24) (e : Fin 6) :
    let a := digit vertexPermutations[v.val]! (edgeVertices e).1.val
    let b := digit vertexPermutations[v.val]! (edgeVertices e).2.val
    a ≠ b ∧ edgeIndex (min a b) (max a b) = digit edgePermutations[v.val]! e.val := by
  dsimp only
  rw [(edge_vertices_code e).1,(edge_vertices_code e).2]
  have h := edge_permutations_induced v e
  dsimp only at h
  have hr := edge_roundtrip ⟨digit edgePermutations[v.val]! e.val,Nat.mod_lt _ (by decide)⟩
  dsimp only at hr
  constructor
  · rw [h.1,h.2] at hr; omega
  · rw [← h.1,← h.2]; exact hr.2

def transformCode (r v c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + digit c (digit r (digit v i))*6^i) 0

def numericEdge (r v c : Nat) (e : Fin 6) : Fin 6 :=
  ⟨digit c (digit r (digit v e.val)),Nat.mod_lt _ (by decide)⟩

theorem transformCode_encode (r v c : Nat) : transformCode r v c = encode (numericEdge r v c) := by
  unfold transformCode
  have hstep : (fun acc i => acc + digit c (digit r (digit v i))*6^i) =
      (fun acc i => acc + 6^i*digit c (digit r (digit v i))) := by
    funext acc i
    rw [Nat.mul_comm (digit c (digit r (digit v i))) (6^i)]
  rw [hstep]
  change 0 + 1*(numericEdge r v c 0).val + 6*(numericEdge r v c 1).val +
    36*(numericEdge r v c 2).val + 216*(numericEdge r v c 3).val +
    1296*(numericEdge r v c 4).val + 7776*(numericEdge r v c 5).val =
    (numericEdge r v c 0).val + 6*(numericEdge r v c 1).val +
    36*(numericEdge r v c 2).val + 216*(numericEdge r v c 3).val +
    1296*(numericEdge r v c 4).val + 7776*(numericEdge r v c 5).val
  simp only [Nat.one_mul,Nat.zero_add]

noncomputable def transformPattern (r : Nat) (v : Fin 24) (c : Fin 60) :=
  fun u w => (fromCode r (vertexPerm4 v u) (vertexPerm4 v w)).map (colorPerm c)

theorem transformPattern_edge (r : Nat) (v : Fin 24) (c : Fin 60) (e : Fin 6) :
    transformPattern r v c (edgeVertices e).1 (edgeVertices e).2 =
      some (numericEdge r edgePermutations[v.val]! colorPermutations[c.val]! e) := by
  have h := table_edge_index v e
  have hn : vertexPerm4 v (edgeVertices e).1 ≠ vertexPerm4 v (edgeVertices e).2 := by
    intro he
    exact h.1 (congrArg Fin.val he)
  simp only [transformPattern,fromCode,if_neg hn,Option.map_some]
  apply congrArg some
  apply Fin.ext
  change digit colorPermutations[c.val]! (digit r (edgeIndex
    (min (digit vertexPermutations[v.val]! (edgeVertices e).1.val)
      (digit vertexPermutations[v.val]! (edgeVertices e).2.val))
    (max (digit vertexPermutations[v.val]! (edgeVertices e).1.val)
      (digit vertexPermutations[v.val]! (edgeVertices e).2.val)))) = _
  rw [h.2]
  rfl

theorem transformPattern_code (r : Nat) (v : Fin 24) (c : Fin 60) :
    patternCode (transformPattern r v c) =
      transformCode r edgePermutations[v.val]! colorPermutations[c.val]! := by
  rw [transformCode_encode]
  simp only [patternCode,transformPattern_edge,Option.getD_some]

noncomputable def tableAction4 (v : Fin 24) (c : Fin 60) : Symmetry (V := Fin 4) colorGroup :=
  ((vertexPerm4 v)⁻¹,⟨colorPerm c,colorPerm_preserves c⟩)

theorem tableAction_pattern (r : Nat) (v : Fin 24) (c : Fin 60) :
    tableAction4 v c • fromCode r = transformPattern r v c := by
  change transport colorGroup (tableAction4 v c) (fromCode r) = _
  funext u w
  simp [transport,tableAction4,transformPattern]

theorem tableAction_code (r : Nat) (v : Fin 24) (c : Fin 60) :
    patternCode (tableAction4 v c • fromCode r) =
      transformCode r edgePermutations[v.val]! colorPermutations[c.val]! := by
  rw [tableAction_pattern,transformPattern_code]

theorem transformed_components (r : Fin 25) (v : Fin 24) (c : Fin 60) :
    transformed (1+c.val+60*v.val+1440*r.val) =
      transformCode representatives[r.val]! edgePermutations[v.val]! colorPermutations[c.val]! := by
  have hsub : 1+c.val+60*v.val+1440*r.val-1 = c.val+60*v.val+1440*r.val := by omega
  have hr : (c.val+60*v.val+1440*r.val)/1440 = r.val := by omega
  have hv : (c.val+60*v.val+1440*r.val)/60%24 = v.val := by omega
  have hc : (c.val+60*v.val+1440*r.val)%60 = c.val := by omega
  simp only [transformed,hsub,hr,hv,hc,transformCode]
end ColeskiPatternFourTransform
#print axioms ColeskiPatternFourTransform.tableAction_code
#print axioms ColeskiPatternFourTransform.transformed_components

/- END bundled local module PatternFourTransform -/

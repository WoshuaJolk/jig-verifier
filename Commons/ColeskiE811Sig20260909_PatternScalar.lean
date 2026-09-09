import Commons.ColeskiE811Sig20260909_PatternCode

/- BEGIN bundled local module PatternScalar -/

namespace ColeskiPatternScalar
open ColeskiPatternCode ColeskiK4Coverage ColeskiK5Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem fromCode_edge (n : Nat) (e : Fin 10) :
    fromCode n (edgeVertices e).1 (edgeVertices e).2 =
      some ⟨digit n e, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases e <;> rfl

theorem code_fromCode (n : Nat) (hn : n < 60466176) : patternCode (fromCode n) = n := by
  norm_num [patternCode, fromCode_edge, encode10, digit]
  omega

theorem representative_bounds : ∀ r : Fin 551, representatives5[r.val]! < 60466176 := by decide

def transformCode (r v c : Nat) : Nat :=
  (List.range 10).foldl (fun acc i => acc + digit c (digit r (v/10^i%10))*6^i) 0

theorem transformed_components (r : Fin 551) (v : Fin 120) (c : Fin 60) :
    transformed5 (1+c.val+60*v.val+7200*r.val) =
      transformCode representatives5[r.val]! edgeMaps5[v.val]! colorPermutations[c.val]! := by
  have hsub : 1+c.val+60*v.val+7200*r.val-1 = c.val+60*v.val+7200*r.val := by omega
  have hr : (c.val+60*v.val+7200*r.val)/7200 = r.val := by omega
  have hv : (c.val+60*v.val+7200*r.val)/60%120 = v.val := by omega
  have hc : (c.val+60*v.val+7200*r.val)%60 = c.val := by omega
  simp only [transformed5, hsub, hr, hv, hc, transformCode]
end ColeskiPatternScalar
#print axioms ColeskiPatternScalar.code_fromCode
#print axioms ColeskiPatternScalar.transformed_components

/- END bundled local module PatternScalar -/

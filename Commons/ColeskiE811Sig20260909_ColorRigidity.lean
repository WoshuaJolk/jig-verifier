import Commons.ColeskiE811Sig20260909_TablePermutations

/- BEGIN bundled local module ColorRigidity -/

namespace ColeskiColorRigidity
open ColeskiK4Coverage ColeskiTablePermutations
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem unique_other_mate : ∀ a b c x y : Fin 6,
    a ≠ b → a ≠ c → b ≠ c → x ≠ a → x ≠ b → x ≠ c →
    y ≠ a → y ≠ b → y ≠ c →
    good a b c = true → good a b x = true → good a b y = true → x = y := by
  decide

theorem triple_table : ∀ a b c : Fin 6,
    a ≠ b → a ≠ c → b ≠ c → good a b c = true →
    ∃ i : Fin 60, digit colorPermutations[i.val]! 0 = a.val ∧
      digit colorPermutations[i.val]! 1 = b.val ∧
      digit colorPermutations[i.val]! 2 = c.val := by
  decide
end ColeskiColorRigidity
#print axioms ColeskiColorRigidity.unique_other_mate
#print axioms ColeskiColorRigidity.triple_table

/- END bundled local module ColorRigidity -/

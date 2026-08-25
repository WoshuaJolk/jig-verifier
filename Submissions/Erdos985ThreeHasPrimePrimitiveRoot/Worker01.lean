import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos985ThreeHasPrimePrimitiveRoot.Worker01

theorem proof :
    ∃ q : ℕ, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 3 - 1 := by
  use 2
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num
  apply orderOf_eq_prime (p := 2)
  · decide
  · decide

end Submissions.Erdos985ThreeHasPrimePrimitiveRoot.Worker01

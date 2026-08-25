import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos1074EightIsEHS.Direct

open scoped Nat

def EHSNumbers : Set ℕ :=
  {m | 1 ≤ m ∧
    ∃ p : ℕ, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m.factorial + 1}

theorem proof : 8 ∈ EHSNumbers := by
  refine ⟨by norm_num, 61, by norm_num, ?_, by norm_num [Nat.factorial]⟩
  norm_num [Nat.ModEq]

end Submissions.Erdos1074EightIsEHS.Direct

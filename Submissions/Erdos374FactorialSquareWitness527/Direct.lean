import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Submissions.Erdos374FactorialSquareWitness527.Direct

def IsSquare (n : ℕ) : Prop := ∃ q : ℕ, n = q ^ 2

theorem proof :
    IsSquare (Nat.factorial 527 * Nat.factorial 526 *
      Nat.factorial 31 * Nat.factorial 30 *
      Nat.factorial 17 * Nat.factorial 16) := by
  refine ⟨527 * Nat.factorial 526 * Nat.factorial 30 * Nat.factorial 16, ?_⟩
  rw [show Nat.factorial 527 = 527 * Nat.factorial 526 by
    simpa using Nat.factorial_succ 526]
  rw [show Nat.factorial 31 = 31 * Nat.factorial 30 by
    simpa using Nat.factorial_succ 30]
  rw [show Nat.factorial 17 = 17 * Nat.factorial 16 by
    simpa using Nat.factorial_succ 16]
  norm_num [pow_two]

end Submissions.Erdos374FactorialSquareWitness527.Direct

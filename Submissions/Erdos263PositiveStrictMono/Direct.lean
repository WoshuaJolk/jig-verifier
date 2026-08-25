import Mathlib.Tactic

namespace Submissions.Erdos263PositiveStrictMono.Direct

theorem proof :
    (∀ n : ℕ, 0 < 2 ^ 2 ^ n) ∧ StrictMono (fun n : ℕ => 2 ^ 2 ^ n) := by
  constructor
  · intro n
    positivity
  · apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.pow_lt_pow_right (by decide)
      (Nat.pow_lt_pow_right (by decide) n.lt_succ_self)

end Submissions.Erdos263PositiveStrictMono.Direct

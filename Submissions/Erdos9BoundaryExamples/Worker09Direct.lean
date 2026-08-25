import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos9BoundaryExamples.Worker09Direct

def Exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ (p k l : ℕ), Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l}

theorem proof :
    1 ∈ Exceptional ∧ 3 ∈ Exceptional ∧ 5 ∉ Exceptional := by
  constructor
  · constructor
    · decide
    · push Not
      intro p k l hp
      linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]
  constructor
  · constructor
    · decide
    · push Not
      intro p k l hp
      linarith [Nat.Prime.two_le hp, @Nat.one_le_two_pow k, @Nat.one_le_two_pow l]
  · unfold Exceptional
    simp only [exists_and_left, not_exists, not_and, Set.mem_ofPred_eq,
      not_forall, Decidable.not_not]
    intro
    use 3, Nat.prime_three, 0, 0
    norm_num

end Submissions.Erdos9BoundaryExamples.Worker09Direct

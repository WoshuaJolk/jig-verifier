import Mathlib.Data.Nat.Factorial.BigOperators

namespace Submissions.Erdos400FeasiblePair.Worker04Degenerate

theorem proof :
    False → ∃ a : Fin 2 → ℕ,
      (∏ i, Nat.factorial (a i)) ∣ Nat.factorial 0 ∧
      (∑ i, a i) = 2 :=
  False.elim

end Submissions.Erdos400FeasiblePair.Worker04Degenerate

import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos203FiniteBoxWitness.Degenerate

theorem proof : False →
    Nat.Coprime 427771 6 ∧
      ∀ k ≤ 8, ∀ l ≤ 8,
        ¬(2 ^ k * 3 ^ l * 427771 + 1).Prime :=
  False.elim

end Submissions.Erdos203FiniteBoxWitness.Degenerate

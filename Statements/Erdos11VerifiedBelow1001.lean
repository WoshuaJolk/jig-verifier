import Mathlib.Data.Nat.Squarefree

namespace Statements.Erdos11VerifiedBelow1001

/-- Kernel-checkable bounded case of Erdős Problem 11. -/
abbrev statement : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → n ≤ 1000 →
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

theorem target : statement := sorry

end Statements.Erdos11VerifiedBelow1001

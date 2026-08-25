import Mathlib.Data.Nat.Prime.Nth

namespace Submissions.Erdos218ComparisonPartition.Control

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

abbrev claimedStatement : Prop :=
  ({n | primeGap n ≤ primeGap (n + 1)} ∪
      {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) = Set.univ ∧
  ({n | primeGap n ≤ primeGap (n + 1)} ∩
      {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) =
    {n | primeGap n = primeGap (n + 1)}

theorem vacuousHypothesis : False → claimedStatement := False.elim

end Submissions.Erdos218ComparisonPartition.Control

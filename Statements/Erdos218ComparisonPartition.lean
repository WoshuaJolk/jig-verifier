import Mathlib.Data.Nat.Prime.Nth

namespace Statements.Erdos218ComparisonPartition

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The two weak comparison events cover all indices and overlap exactly
at indices with equal consecutive prime gaps. -/
abbrev statement : Prop :=
  ({n | primeGap n ≤ primeGap (n + 1)} ∪
      {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) = Set.univ ∧
  ({n | primeGap n ≤ primeGap (n + 1)} ∩
      {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) =
    {n | primeGap n = primeGap (n + 1)}

theorem target : statement := sorry

end Statements.Erdos218ComparisonPartition

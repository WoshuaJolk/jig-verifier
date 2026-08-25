import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace Submissions.Erdos218ComparisonPartition.Direct

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

theorem proof :
    ({n | primeGap n ≤ primeGap (n + 1)} ∪
        {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) = Set.univ ∧
    ({n | primeGap n ≤ primeGap (n + 1)} ∩
        {n | primeGap (n + 1) ≤ primeGap n} : Set ℕ) =
      {n | primeGap n = primeGap (n + 1)} := by
  constructor
  · ext n
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    omega
  · ext n
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    omega

end Submissions.Erdos218ComparisonPartition.Direct

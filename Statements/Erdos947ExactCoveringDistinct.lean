import Mathlib.Data.Int.ModEq

namespace Statements.Erdos947ExactCoveringDistinct

/-- A finite list of normalized congruence classes that partitions the integers. -/
abbrev IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length,
    let (a, n) := l.get i
    m ≡ a [ZMOD n])

/-- The Mirsky–Newman/Davenport–Rado answer to Erdős Problem 947. -/
abbrev statement : Prop :=
  ¬ ∃ l : List (ℤ × ℕ),
    IsExactCoveringSystem l ∧
    l.Pairwise (fun p q => p.2 ≠ q.2) ∧
    l.length ≥ 2

theorem target : statement := sorry

end Statements.Erdos947ExactCoveringDistinct

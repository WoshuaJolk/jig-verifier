import Mathlib.Tactic

namespace Statements.Erdos287TwoTermCase

def maxGap (s : Fin 2 → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin 1 =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- The two-denominator case of Erdős 287. -/
abbrev statement : Prop :=
  ∀ s : Fin 2 → ℕ,
    StrictMono s →
    1 < s 0 →
    ∑ i : Fin 2, 1 / (s i : ℝ) = 1 →
    3 ≤ maxGap s

theorem target : statement := sorry

end Statements.Erdos287TwoTermCase

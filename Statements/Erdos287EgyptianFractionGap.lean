import Mathlib.Tactic

namespace Statements.Erdos287EgyptianFractionGap

def maxGap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin (k - 1) =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- Erdős Problem 287: an Egyptian fraction expansion of one by distinct
increasing denominators greater than one has a gap of at least three. -/
abbrev statement : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s →
    1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    3 ≤ maxGap k s

theorem target : statement := sorry

end Statements.Erdos287EgyptianFractionGap

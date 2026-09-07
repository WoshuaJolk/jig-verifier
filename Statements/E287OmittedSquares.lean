import Mathlib.Tactic
namespace Statements.E287OmittedSquares
def maxGap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin (k-1) =>
    s ⟨i.val+1, by omega⟩ - s ⟨i.val, by omega⟩)
abbrev statement : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s →
    1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1/(s i : ℝ) = 1 →
    (∀ i : Fin k, ¬4 ∣ s i) →
    (∀ i : Fin k, ¬9 ∣ s i) →
    3 ≤ maxGap k s
theorem target : statement := sorry
end Statements.E287OmittedSquares

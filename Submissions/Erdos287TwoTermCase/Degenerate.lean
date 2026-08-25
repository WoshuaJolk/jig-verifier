import Mathlib.Tactic

namespace Submissions.Erdos287TwoTermCase.Degenerate

def maxGap (s : Fin 2 → ℕ) : ℕ :=
  Finset.sup Finset.univ (fun i : Fin 1 =>
    s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

theorem proof : False →
    ∀ s : Fin 2 → ℕ,
      StrictMono s →
      1 < s 0 →
      ∑ i : Fin 2, 1 / (s i : ℝ) = 1 →
      3 ≤ maxGap s :=
  False.elim

end Submissions.Erdos287TwoTermCase.Degenerate

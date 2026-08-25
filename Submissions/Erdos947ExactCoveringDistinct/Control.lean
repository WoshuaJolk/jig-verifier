import Mathlib.Data.Int.ModEq

namespace Submissions.Erdos947ExactCoveringDistinct.Control

abbrev IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length,
    let (a, n) := l.get i
    m ≡ a [ZMOD n])

theorem proof (h : False) :
    ¬ ∃ l : List (ℤ × ℕ),
      IsExactCoveringSystem l ∧
      l.Pairwise (fun p q => p.2 ≠ q.2) ∧
      l.length ≥ 2 :=
  h.elim

end Submissions.Erdos947ExactCoveringDistinct.Control

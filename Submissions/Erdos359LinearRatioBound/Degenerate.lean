import Mathlib.Tactic

namespace Submissions.Erdos359LinearRatioBound.Degenerate

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop :=
  A 0 = n ∧ StrictMono A ∧
    ∀ j, IsLeast
      {m : ℕ | A j < m ∧
        ∀ a b, Finset.Icc a b ⊆ Finset.Iic j →
          m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (A (j + 1))

theorem proof : False →
    ∀ A : ℕ → ℕ, IsGoodFor A 1 →
      ∀ k ≥ 1, (1 : ℝ) ≤ (A k : ℝ) / k :=
  False.elim

end Submissions.Erdos359LinearRatioBound.Degenerate

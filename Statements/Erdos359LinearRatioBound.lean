import Mathlib.Tactic

namespace Statements.Erdos359LinearRatioBound

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop :=
  A 0 = n ∧ StrictMono A ∧
    ∀ j, IsLeast
      {m : ℕ | A j < m ∧
        ∀ a b, Finset.Icc a b ⊆ Finset.Iic j →
          m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (A (j + 1))

/-- The ratio in Erdős 359(i) is at least one at every positive index. -/
abbrev statement : Prop :=
  ∀ A : ℕ → ℕ, IsGoodFor A 1 →
    ∀ k ≥ 1, (1 : ℝ) ≤ (A k : ℝ) / k

theorem target : statement := sorry

end Statements.Erdos359LinearRatioBound

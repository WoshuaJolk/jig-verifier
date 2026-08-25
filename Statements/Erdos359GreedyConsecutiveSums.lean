import Mathlib.Tactic

open Filter

namespace Statements.Erdos359GreedyConsecutiveSums

/-- `A` starts at `n`, is strictly increasing, and each next term is the
least integer not representable by a consecutive block of earlier terms. -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop :=
  A 0 = n ∧ StrictMono A ∧
    ∀ j, IsLeast
      {m : ℕ | A j < m ∧
        ∀ a b, Finset.Icc a b ⊆ Finset.Iic j →
          m ≠ ∑ i ∈ Finset.Icc a b, A i}
      (A (j + 1))

/-- Erdős Problem 359(i): the greedy sequence beginning at one grows
superlinearly. -/
abbrev statement : Prop :=
  ∀ A : ℕ → ℕ, IsGoodFor A 1 →
    atTop.Tendsto (fun k => (A k : ℝ) / k) atTop

theorem target : statement := sorry

end Statements.Erdos359GreedyConsecutiveSums

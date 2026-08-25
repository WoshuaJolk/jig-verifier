import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14UniformStability

open scoped BigOperators

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

noncomputable def upperBlock (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (M + 1) (2 * M)).filter fun a => a ∈ A

noncomputable def crossPairs (A : Set ℕ) (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  exact (B ×ˢ C) ∪ (C ×ˢ B)

noncomputable def crossRepCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  exact ((crossPairs A M).filter fun p => p.1 + p.2 = n).card

noncomputable def crossEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.Icc (M + 1) (3 * M), (crossRepCount A M n) ^ 2

def uniformCross (A : Set ℕ) (M : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc (M + 1) (3 * M),
    ∀ j ∈ Finset.Icc (M + 1) (3 * M),
      crossRepCount A M i = crossRepCount A M j

/-- Exact classification of Cauchy equality for adjacent-block convolution,
and the resulting integral stability gap away from uniformity. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (M : ℕ), 0 < M →
    let k := (initialSegment A M).card
    let l := (upperBlock A M).card
    let X := crossEnergy A M
    (2 * M * X = 4 * (k * l) ^ 2 ↔ uniformCross A M) ∧
    (¬ uniformCross A M → 4 * (k * l) ^ 2 + 1 ≤ 2 * M * X)

theorem target : statement := sorry

end Statements.Erdos14UniformStability

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14MultiscaleEnergy

open scoped BigOperators

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

noncomputable def upperBlock (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (M + 1) (2 * M)).filter fun a => a ∈ A

noncomputable def repCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  let B := initialSegment A M
  exact ((B ×ˢ B).filter fun p => p.1 + p.2 = n).card

noncomputable def additiveEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.range (2 * M + 1), (repCount A M n) ^ 2

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

/-- Two-scale energy growth and the sharp Cauchy lower bound for the
cross-block contribution. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (M : ℕ),
    additiveEnergy A M + crossEnergy A M ≤ additiveEnergy A (2 * M) ∧
    4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 ≤
      2 * M * crossEnergy A M

theorem target : statement := sorry

end Statements.Erdos14MultiscaleEnergy

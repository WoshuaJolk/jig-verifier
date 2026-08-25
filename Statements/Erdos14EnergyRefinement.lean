import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14EnergyRefinement

open scoped BigOperators

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionNat (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n => n ∉ uniquePairSums A).card

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

/-- Number of ordered pairs from `A ∩ [0,M]` summing to `n`. -/
noncomputable def repCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  let B := initialSegment A M
  exact ((B ×ˢ B).filter fun p => p.1 + p.2 = n).card

/-- Additive energy of the ordered representation counts on `[0,2M]`. -/
noncomputable def additiveEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.range (2 * M + 1), (repCount A M n) ^ 2

/-- Energy refinement of the finite density bound. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (M : ℕ),
    let B := initialSegment A M
    let E := exceptionNat A (2 * M)
    additiveEnergy A M + 4 * E ≤ 8 * M + 1 + B.card ^ 2 * E

theorem target : statement := sorry

end Statements.Erdos14EnergyRefinement

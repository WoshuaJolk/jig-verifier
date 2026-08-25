import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos14DensityTradeoff

/-- Natural numbers having exactly one unordered representation as a
sum of two elements of `A`. -/
def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

/-- The number of positive exceptions up to `N`, as a natural number. -/
noncomputable def exceptionNat (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter fun n => n ∉ uniquePairSums A).card

/-- Elements of `A` in `[0,M]`. -/
noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 0 M).filter fun a => a ∈ A

/-- A finite density--exception tradeoff: ordered pairs from the initial
segment must land either in a unique sum or in an exceptional sum. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (M : ℕ),
    let k := (initialSegment A M).card
    k * k ≤ 2 * (2 * M + 1) + k * exceptionNat A (2 * M)

theorem target : statement := sorry

end Statements.Erdos14DensityTradeoff

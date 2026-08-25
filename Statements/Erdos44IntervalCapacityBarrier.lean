import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Statements.Erdos44IntervalCapacityBarrier

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- A Sidon set in `[R,L]` has at most `2(L-R)` ordered distinct pairs. -/
abbrev statement : Prop :=
  ∀ (R L : ℕ) (C : Finset ℕ), R ≤ L →
    C ⊆ Finset.Icc R L → IsSidon (C : Set ℕ) →
      C.card * C.card - C.card ≤ 2 * (L - R)

theorem target : statement := by
  sorry

end Statements.Erdos44IntervalCapacityBarrier

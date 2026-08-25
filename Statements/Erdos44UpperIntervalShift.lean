import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Statements.Erdos44UpperIntervalShift

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def CrossUnique (A C : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

/-- An upper-interval Sidon block can be adjoined with an arbitrary shift once
the exact old/mixed and mixed/block sum-range inequalities hold. -/
abbrev statement : Prop :=
  ∀ (N R L t : ℕ) (A C : Finset ℕ), 1 ≤ N → R ≤ L →
    2 * N < t + R + 1 → N + L < t + 2 * R →
    A ⊆ Finset.Icc 1 N → C ⊆ Finset.Icc R L →
    IsSidon (A : Set ℕ) → IsSidon (C : Set ℕ) → CrossUnique A C →
      let B := C.image (fun c => t + c)
      B ⊆ Finset.Icc (N + 1) (t + L) ∧
        B.card = C.card ∧
          (A ∪ B).card = A.card + C.card ∧
            IsSidon (A ∪ B : Set ℕ)

theorem target : statement := by
  sorry

end Statements.Erdos44UpperIntervalShift

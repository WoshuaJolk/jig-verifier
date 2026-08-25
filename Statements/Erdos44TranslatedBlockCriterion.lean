import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44TranslatedBlockCriterion

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

def CrossUnique (A C : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

/-- Difference compatibility is the exact remaining condition after separating the three sum zones. -/
abbrev statement : Prop :=
  ∀ᵉ (N ≥ (1 : ℕ)) (L ≥ N)
    (A ⊆ Finset.Icc 1 N) (C ⊆ Finset.Icc 1 L),
      IsSidon (A : Set ℕ) → IsSidon (C : Set ℕ) → CrossUnique A C →
        let T := N + L
        let B := C.image (fun c => T + c)
        B ⊆ Finset.Icc (N + 1) (N + 2 * L) ∧
          B.card = C.card ∧
            (A ∪ B).card = A.card + C.card ∧
              IsSidon (A ∪ B : Set ℕ)

theorem target : statement := sorry

end Statements.Erdos44TranslatedBlockCriterion

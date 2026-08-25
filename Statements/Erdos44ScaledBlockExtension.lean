import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44ScaledBlockExtension

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- A whole Sidon block can be adjoined after scaling by `2N`, with polynomial support. -/
abbrev statement : Prop :=
  ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
    ∀ᵉ (L ≥ (1 : ℕ)) (C ⊆ Finset.Icc 1 L), IsSidon (C : Set ℕ) →
      let B := C.image (fun c => (2 * N) * c)
      N < 2 * N * L ∧
        B ⊆ Finset.Icc (N + 1) (2 * N * L) ∧
          B.card = C.card ∧
            (A ∪ B).card = A.card + C.card ∧
              IsSidon (A ∪ B : Set ℕ)

theorem target : statement := sorry

end Statements.Erdos44ScaledBlockExtension

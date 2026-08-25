import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt

namespace Statements.Erdos44PolynomialSidonBlocks

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

/-- An explicit `k`-point Sidon block with cubic support. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let q := 2 * k + 1
    let L := k + q * k^2
    let C := (Finset.Icc 1 k).image (fun i => i + q * i^2)
    C ⊆ Finset.Icc 1 L ∧ C.card = k ∧ IsSidon (C : Set ℕ)

theorem target : statement := sorry

end Statements.Erdos44PolynomialSidonBlocks

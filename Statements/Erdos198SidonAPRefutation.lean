import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card

namespace Statements.Erdos198SidonAPRefutation

abbrev statement : Prop :=
  ¬ ∀ A : Set ℕ,
    (∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
      i₁ + i₂ = j₁ + j₂ →
        (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) →
    ∃ Y : Set ℕ,
      (∃ a d : ℕ, ENat.card Y = ⊤ ∧
        Y = {a + n • d | (n : ℕ) (_ : n < (⊤ : ℕ∞))}) ∧
      Y ⊆ Aᶜ

theorem target : statement := sorry

end Statements.Erdos198SidonAPRefutation

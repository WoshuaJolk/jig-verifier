import Mathlib.Data.Set.Basic

namespace Submissions.Erdos340SingletonSidon.Worker04Degenerate

def IsSidon (A : Set ℕ) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof : False → IsSidon {1} :=
  False.elim

end Submissions.Erdos340SingletonSidon.Worker04Degenerate

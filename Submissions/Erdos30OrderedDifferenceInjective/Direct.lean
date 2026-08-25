import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Submissions.Erdos30OrderedDifferenceInjective.Direct

def IsSidon (A : Set ℕ) : Prop :=
  ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof :
    ∀ A : Set ℕ, IsSidon A →
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a < b → c < d → b - a = d - c → a = c ∧ b = d := by
  intro A hA a ha b hb c hc d hd hab hcd hdiff
  have hsum : b + c = d + a := by omega
  rcases hA b hb d hd c hc a ha hsum with h | h
  · exact ⟨h.2.symm, h.1⟩
  · omega

end Submissions.Erdos30OrderedDifferenceInjective.Direct

import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Submissions.Erdos44OnePointExtension.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof :
    ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) → ∀ (x : ℕ), 2 * N ≤ x →
        IsSidon ((A : Set ℕ) ∪ {x}) := by
  intro N A hsub hsidon x hx
  have upper : ∀ ⦃a : ℕ⦄, a ∈ A → a ≤ N := by
    intro a ha
    exact (Finset.mem_Icc.mp (hsub ha)).2
  have lower : ∀ ⦃a : ℕ⦄, a ∈ A → 1 ≤ a := by
    intro a ha
    exact (Finset.mem_Icc.mp (hsub ha)).1
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_union, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  rcases hi₁ with hi₁ | rfl <;>
    rcases hj₁ with hj₁ | rfl <;>
      rcases hi₂ with hi₂ | rfl <;>
        rcases hj₂ with hj₂ | rfl
  all_goals
    try have hi₁N := upper hi₁
    try have hj₁N := upper hj₁
    try have hi₂N := upper hi₂
    try have hj₂N := upper hj₂
    try have hi₁pos := lower hi₁
    try have hj₁pos := lower hj₁
    try have hi₂pos := lower hi₂
    try have hj₂pos := lower hj₂
    first
    | exact hsidon i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    | (left; constructor <;> omega)
    | (right; constructor <;> omega)
    | omega

end Submissions.Erdos44OnePointExtension.Direct

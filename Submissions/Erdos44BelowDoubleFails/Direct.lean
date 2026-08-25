import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44BelowDoubleFails.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

theorem proof :
    ∀ (N : ℕ), 2 ≤ N →
      ({1, N} : Finset ℕ) ⊆ Finset.Icc 1 N ∧
        IsSidon ({1, N} : Set ℕ) ∧
          ¬ IsSidon (({1, N} : Set ℕ) ∪ {2 * N - 1}) := by
  intro N hN
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> exact Finset.mem_Icc.mpr (by omega)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
    rcases hi₁ with rfl | rfl <;>
      rcases hj₁ with rfl | rfl <;>
        rcases hi₂ with rfl | rfl <;>
          rcases hj₂ with rfl | rfl <;> simp_all <;> omega
  · intro h
    have bad := h 1 (by simp) N (by simp) (2 * N - 1) (by simp) N (by simp)
      (by omega)
    rcases bad with hbad | hbad <;> omega

end Submissions.Erdos44BelowDoubleFails.Direct

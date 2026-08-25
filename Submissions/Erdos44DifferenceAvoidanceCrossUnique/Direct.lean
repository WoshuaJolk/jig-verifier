import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44DifferenceAvoidanceCrossUnique.Direct

open Set Finset

def PositiveDifferences (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter fun p => p.1 < p.2).image fun p => p.2 - p.1

def AvoidsDifferences (C F : Finset ℕ) : Prop :=
  ∀ x ∈ C, ∀ d ∈ F, x + d ∉ C

def CrossUnique (A C : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ c₁ ∈ C, ∀ c₂ ∈ C,
    a₁ + c₁ = a₂ + c₂ → a₁ = a₂ ∧ c₁ = c₂

theorem proof :
    ∀ A C : Finset ℕ,
      AvoidsDifferences C (PositiveDifferences A) → CrossUnique A C := by
  intro A C hAvoid
  intro a₁ ha₁ a₂ ha₂ c₁ hc₁ c₂ hc₂ hsum
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · exfalso
    let d := a₂ - a₁
    have hd : d ∈ PositiveDifferences A := by
      apply Finset.mem_image.mpr
      refine ⟨(a₁, a₂), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha₁, ha₂⟩, hlt⟩
    have hcd : c₂ + d = c₁ := by
      dsimp [d]
      omega
    exact (hAvoid c₂ hc₂ d hd) (by simpa [hcd] using hc₁)
  · subst a₂
    exact ⟨rfl, by omega⟩
  · exfalso
    let d := a₁ - a₂
    have hd : d ∈ PositiveDifferences A := by
      apply Finset.mem_image.mpr
      refine ⟨(a₂, a₁), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha₂, ha₁⟩, hgt⟩
    have hcd : c₁ + d = c₂ := by
      dsimp [d]
      omega
    exact (hAvoid c₁ hc₁ d hd) (by simpa [hcd] using hc₂)

end Submissions.Erdos44DifferenceAvoidanceCrossUnique.Direct

import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Submissions.Erdos44ShiftCollisionBound.Direct

open Set Finset

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ →
      (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

abbrev ShiftWitness := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

def ShiftCollisions (S A C : Finset ℕ) : Finset ShiftWitness :=
  ((((S ×ˢ A) ×ˢ C) ×ˢ C) ×ˢ C).filter fun p =>
    p.1.2 ≤ p.2 ∧
      p.1.1.1.2 + (p.1.1.1.1 + p.1.1.2) =
        2 * p.1.1.1.1 + p.1.2 + p.2

theorem proof :
    ∀ (S A C : Finset ℕ), IsSidon (C : Set ℕ) →
      (ShiftCollisions S A C).card ≤ S.card * A.card * C.card := by
  classical
  intro S A C hC
  let proj : ShiftWitness → ((ℕ × ℕ) × ℕ) :=
    fun p => ((p.1.1.1.1, p.1.1.1.2), p.1.1.2)
  have hinj : Set.InjOn proj (ShiftCollisions S A C) := by
    rintro ⟨⟨⟨⟨tx, ax⟩, cx⟩, x₁⟩, x₂⟩ hx
      ⟨⟨⟨⟨ty, ay⟩, cy⟩, y₁⟩, y₂⟩ hy hproj
    unfold ShiftCollisions at hx hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    simp only [Finset.mem_product] at hx' hy'
    rcases hx' with ⟨⟨⟨⟨⟨htx, hax⟩, hcx⟩, hx₁⟩, hx₂⟩, hxord, hxeq⟩
    rcases hy' with ⟨⟨⟨⟨⟨hty, hay⟩, hcy⟩, hy₁⟩, hy₂⟩, hyord, hyeq⟩
    change ((tx, ax), cx) = ((ty, ay), cy) at hproj
    simp only [Prod.mk.injEq] at hproj
    rcases hproj with ⟨⟨rfl, rfl⟩, rfl⟩
    have hsum : x₁ + x₂ = y₁ + y₂ := by omega
    rcases hC x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum with h | h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨hxy₂, hx₂y⟩
      congr <;> omega
  have himage :
      ((ShiftCollisions S A C).image proj).card =
        (ShiftCollisions S A C).card :=
    Finset.card_image_of_injOn hinj
  have hsubset :
      (ShiftCollisions S A C).image proj ⊆ ((S ×ˢ A) ×ˢ C) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    unfold ShiftCollisions at hp
    have hp' := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_product] at hp'
    rcases hp' with ⟨⟨⟨hpSA, hpC⟩, -⟩, -⟩
    simp only [Finset.mem_product]
    exact ⟨hpSA, hpC⟩
  calc
    (ShiftCollisions S A C).card =
        ((ShiftCollisions S A C).image proj).card := himage.symm
    _ ≤ ((S ×ˢ A) ×ˢ C).card := Finset.card_le_card hsubset
    _ = S.card * A.card * C.card := by simp [mul_assoc]

end Submissions.Erdos44ShiftCollisionBound.Direct

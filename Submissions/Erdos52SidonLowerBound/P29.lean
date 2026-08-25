import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Submissions.Erdos52SidonLowerBound.P29

theorem proof :
    ∀ A : Finset ℤ,
      (∀ a ∈ A, ∀ b ∈ A, a ≤ b →
        ∀ c ∈ A, ∀ d ∈ A, c ≤ d →
          a + b = c + d → a = c ∧ b = d) →
      (A + A).card = A.card + A.card.choose 2 := by
  classical
  intro A hSidon
  let P : Finset (ℤ × ℤ) :=
    A.diag ∪ (A ×ˢ A).filter fun p => p.1 < p.2
  have hmem (p : ℤ × ℤ) (hp : p ∈ P) :
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 := by
    simp only [P, Finset.mem_union, Finset.mem_diag, Finset.mem_filter,
      Finset.mem_product] at hp
    rcases hp with hp | hp
    · exact ⟨hp.1, hp.2 ▸ hp.1, hp.2.le⟩
    · exact ⟨hp.1.1, hp.1.2, hp.2.le⟩
  have hdisj :
      Disjoint A.diag ((A ×ˢ A).filter fun p => p.1 < p.2) := by
    simp [Finset.disjoint_left]
  have hcard : P.card = A.card + A.card.choose 2 := by
    dsimp only [P]
    rw [Finset.card_union_of_disjoint hdisj, Finset.diag_card,
      Finset.card_product_filter_lt]
  let f : ℤ × ℤ → ℤ := fun p => p.1 + p.2
  have hinj : Set.InjOn f P := by
    intro x hx y hy hxy
    obtain ⟨hx₁, hx₂, hxle⟩ := hmem x hx
    obtain ⟨hy₁, hy₂, hyle⟩ := hmem y hy
    have h := hSidon x.1 hx₁ x.2 hx₂ hxle y.1 hy₁ y.2 hy₂ hyle hxy
    exact Prod.ext h.1 h.2
  have himage : (P.image f).card = P.card :=
    Finset.card_image_of_injOn hinj
  have hsubset : P.image f ⊆ A + A := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨hp₁, hp₂, -⟩ := hmem p hp
    exact Finset.add_mem_add hp₁ hp₂
  have hsupset : A + A ⊆ P.image f := by
    intro z hz
    simp only [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    by_cases hab : a ≤ b
    · apply Finset.mem_image.mpr
      refine ⟨(a, b), ?_, rfl⟩
      simp [P, ha, hb, hab.eq_or_lt]
    · apply Finset.mem_image.mpr
      refine ⟨(b, a), ?_, add_comm b a⟩
      simp [P, ha, hb, lt_of_not_ge hab]
  have heq : P.image f = A + A :=
    Finset.Subset.antisymm hsubset hsupset
  calc
    (A + A).card = (P.image f).card := congrArg Finset.card heq.symm
    _ = P.card := himage
    _ = A.card + A.card.choose 2 := hcard

end Submissions.Erdos52SidonLowerBound.P29

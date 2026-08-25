import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic

open scoped Pointwise

namespace Submissions.Erdos52CoprimeProductGrowth.P29

/--
If `P` is a pairwise-coprime upper layer of positive naturals and every
element of `B` is positive and smaller than every element of `P`, then all
cross-products `p*b` are distinct.  Consequently their integer casts give
`|P||B|` distinct products in the ambient integer product set.
-/
theorem proof :
    ∀ A P B : Finset ℕ,
      P ⊆ A →
      B ⊆ A →
      (∀ p ∈ P, 0 < p) →
      (∀ b ∈ B, 0 < b) →
      (∀ p ∈ P, ∀ b ∈ B, b < p) →
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Nat.Coprime p q) →
      P.card * B.card ≤
        ((A.image fun n : ℕ => (n : ℤ)) *
          (A.image fun n : ℕ => (n : ℤ))).card := by
  classical
  intro A P B hPA hBA hPpos hBpos hlt hcop
  let S : Finset (ℕ × ℕ) := P ×ˢ B
  let f : ℕ × ℕ → ℤ := fun x => (x.1 : ℤ) * (x.2 : ℤ)
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have hx' : x.1 ∈ P ∧ x.2 ∈ B := by simpa [S] using hx
    have hy' : y.1 ∈ P ∧ y.2 ∈ B := by simpa [S] using hy
    have hnat : x.1 * x.2 = y.1 * y.2 := by
      dsimp [f] at hxy
      exact_mod_cast hxy
    by_cases hpq : x.1 = y.1
    · apply Prod.ext hpq
      apply Nat.mul_left_cancel (hPpos x.1 hx'.1)
      simpa [hpq] using hnat
    · have hdiv : x.1 ∣ y.1 * y.2 := ⟨x.2, hnat.symm⟩
      have hdiv' : x.1 ∣ y.2 :=
        (hcop x.1 hx'.1 y.1 hy'.1 hpq).dvd_of_dvd_mul_left hdiv
      have hle : x.1 ≤ y.2 :=
        Nat.le_of_dvd (hBpos y.2 hy'.2) hdiv'
      exact False.elim ((Nat.not_le_of_lt (hlt x.1 hx'.1 y.2 hy'.2)) hle)
  have hcard : (S.image f).card = P.card * B.card := by
    rw [Finset.card_image_of_injOn hinj]
    simp [S]
  have hsubset :
      S.image f ⊆
        (A.image fun n : ℕ => (n : ℤ)) *
          (A.image fun n : ℕ => (n : ℤ)) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hx' : x.1 ∈ P ∧ x.2 ∈ B := by simpa [S] using hx
    apply Finset.mul_mem_mul
    · exact Finset.mem_image.mpr ⟨x.1, hPA hx'.1, rfl⟩
    · exact Finset.mem_image.mpr ⟨x.2, hBA hx'.2, rfl⟩
  rw [← hcard]
  exact Finset.card_le_card hsubset

end Submissions.Erdos52CoprimeProductGrowth.P29

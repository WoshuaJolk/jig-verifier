import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Submissions.Erdos12ModularPairClassification.NegationTransversal

/-- A complete residue window under the recursive-anchor condition is not a
classically sum-free set.  It is a partial transversal of the involution
`x ↦ m-x`.  At equality it is a complete transversal, with the midpoint
included when `m` is even. -/
theorem proof :
    ∀ (m : ℕ) (D : Finset ℕ),
      (∀ x ∈ D, 0 < x ∧ x < m) →
      (∀ x ∈ D, ∀ y ∈ D, x + y = m → x = y) →
      D.card ≤ m / 2 ∧
        (D.card = m / 2 →
          (∀ x, 0 < x → x < m →
            (x ∈ D ∨ m - x ∈ D) ∧
              (x ≠ m - x → ¬ (x ∈ D ∧ m - x ∈ D))) ∧
          (m % 2 = 0 → 0 < m → m / 2 ∈ D)) ∧
        (∀ x, 0 < x → x < m →
          x ∉ D → m - x ∉ D → D.card < m / 2) := by
  intro m D hD hpairs
  let f : ℕ → ℕ := fun x ↦ min x (m - x)
  have hf_maps : D.image f ⊆ Finset.Ioc 0 (m / 2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx0, hxm⟩ := hD x hx
    have href0 : 0 < m - x := by omega
    have hupper : min x (m - x) ≤ m / 2 := by
      rcases le_total x (m - x) with h | h
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right h]
        omega
    exact Finset.mem_Ioc.mpr ⟨lt_min hx0 href0, hupper⟩
  have hf_inj : Set.InjOn f D := by
    intro x hx y hy hxy
    obtain ⟨hx0, hxm⟩ := hD x hx
    obtain ⟨hy0, hym⟩ := hD y hy
    dsimp [f] at hxy
    by_cases hxside : x ≤ m - x
    · rw [min_eq_left hxside] at hxy
      by_cases hyside : y ≤ m - y
      · rw [min_eq_left hyside] at hxy
        exact hxy
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        apply hpairs x hx y hy
        omega
    · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hxy
      by_cases hyside : y ≤ m - y
      · rw [min_eq_left hyside] at hxy
        apply hpairs x hx y hy
        omega
      · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hxy
        omega
  have hcard : D.card ≤ m / 2 := by
    calc
      D.card = (D.image f).card := (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ (Finset.Ioc 0 (m / 2)).card := Finset.card_le_card hf_maps
      _ = m / 2 := by simp
  have hclass :
      D.card = m / 2 →
        ∀ x, 0 < x → x < m →
          (x ∈ D ∨ m - x ∈ D) ∧
            (x ≠ m - x → ¬ (x ∈ D ∧ m - x ∈ D)) := by
    intro hmax x hx0 hxm
    have himage_eq : D.image f = Finset.Ioc 0 (m / 2) := by
      apply Finset.eq_of_subset_of_card_le hf_maps
      rw [Finset.card_image_of_injOn hf_inj, hmax]
      simp
    have hfx : f x ∈ Finset.Ioc 0 (m / 2) := by
      have href0 : 0 < m - x := by omega
      have hupper : min x (m - x) ≤ m / 2 := by
        rcases le_total x (m - x) with h | h
        · rw [min_eq_left h]
          omega
        · rw [min_eq_right h]
          omega
      exact Finset.mem_Ioc.mpr
        ⟨by simpa [f] using lt_min hx0 href0, by
          change min x (m - x) ≤ m / 2
          exact hupper⟩
    rw [← himage_eq] at hfx
    obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hfx
    obtain ⟨hy0, hym⟩ := hD y hy
    have hyclass : y = x ∨ y = m - x := by
      dsimp [f] at hfy
      by_cases hxside : x ≤ m - x
      · rw [min_eq_left hxside] at hfy
        by_cases hyside : y ≤ m - y
        · rw [min_eq_left hyside] at hfy
          exact Or.inl hfy
        · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hfy
          right
          omega
      · rw [min_eq_right (Nat.le_of_not_ge hxside)] at hfy
        by_cases hyside : y ≤ m - y
        · rw [min_eq_left hyside] at hfy
          right
          omega
        · rw [min_eq_right (Nat.le_of_not_ge hyside)] at hfy
          left
          omega
    constructor
    · rcases hyclass with rfl | h
      · exact Or.inl hy
      · exact Or.inr (by simpa [h] using hy)
    · intro hnot hboth
      apply hnot
      apply hpairs x hboth.1 (m - x) hboth.2
      omega
  refine ⟨hcard, ?_, ?_⟩
  · intro hmax
    refine ⟨hclass hmax, ?_⟩
    intro heven hm0
    have hmid0 : 0 < m / 2 := by omega
    have hmidm : m / 2 < m := by omega
    rcases (hclass hmax (m / 2) hmid0 hmidm).1 with h | h
    · exact h
    · have hsub : m - m / 2 = m / 2 := by omega
      rwa [hsub] at h
  · intro x hx0 hxm hxnot hrefnot
    by_contra hnlt
    have hmax : D.card = m / 2 := by omega
    rcases (hclass hmax x hx0 hxm).1 with h | h
    · exact hxnot h
    · exact hrefnot h

end Submissions.Erdos12ModularPairClassification.NegationTransversal

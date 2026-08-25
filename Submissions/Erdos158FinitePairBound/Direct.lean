import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Submissions.Erdos158FinitePairBound.Direct

open Finset

def B2 (g : ℕ) (A : Set ℕ) : Prop :=
  ∀ n, {x : ℕ × ℕ |
    x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A}.encard ≤ g

theorem proof : ∀ (S : Finset ℕ) (N : ℕ),
    (∀ a ∈ S, a < N) → B2 2 (S : Set ℕ) →
      #((S ×ˢ S).filter fun p => p.1 ≤ p.2) ≤ 4 * N := by
  intro S N hSN hB2
  let P := (S ×ˢ S).filter fun p => p.1 ≤ p.2
  have hmaps : ∀ p ∈ P, p.1 + p.2 ∈ Finset.range (2 * N) := by
    rintro ⟨a, b⟩ hp
    simp only [P, mem_filter, mem_product] at hp
    simp only [mem_range]
    have ha := hSN a hp.1.1
    have hb := hSN b hp.1.2
    omega
  have hfiber : ∀ n ∈ Finset.range (2 * N),
      #{p ∈ P | p.1 + p.2 = n} ≤ 2 := by
    intro n hn
    have hsubset :
        (↑({p ∈ P | p.1 + p.2 = n} : Finset (ℕ × ℕ)) :
          Set (ℕ × ℕ)) ⊆
        {p : ℕ × ℕ |
          p.1 + p.2 = n ∧ p.1 ≤ p.2 ∧ p.1 ∈ (S : Set ℕ) ∧
            p.2 ∈ (S : Set ℕ)} := by
      intro p hp
      simp only [mem_coe, mem_filter] at hp
      simp only [Set.mem_setOf_eq, P, mem_filter, mem_product] at hp ⊢
      exact ⟨hp.2, hp.1.2, hp.1.1.1, hp.1.1.2⟩
    have henc := (Set.encard_le_encard hsubset).trans (hB2 n)
    norm_cast at henc
  have h :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfiber
  simp only [card_range] at h
  change #((S ×ˢ S).filter fun p => p.1 ≤ p.2) ≤ 2 * (2 * N) at h
  omega

end Submissions.Erdos158FinitePairBound.Direct

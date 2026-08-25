import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Prod

open scoped Pointwise

namespace Submissions.Erdos52SidonEnergyObstruction.P29

private theorem two_mul_card_add_choose_two (n : ℕ) :
    2 * (n + n.choose 2) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      change 2 * (n + 1 + (n + n.choose 2)) = (n + 1) * (n + 2)
      calc
        2 * (n + 1 + (n + n.choose 2)) =
            2 * (n + n.choose 2) + 2 * (n + 1) := by omega
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 2) * (n + 1) := (Nat.add_mul n 2 (n + 1)).symm
        _ = (n + 1) * (n + 2) := Nat.mul_comm _ _

private theorem sidon_sumset_card
    (B : Finset ℤ)
    (hSidon :
      ∀ a ∈ B, ∀ b ∈ B, a ≤ b →
        ∀ c ∈ B, ∀ d ∈ B, c ≤ d →
          a + b = c + d → a = c ∧ b = d) :
    (B + B).card = B.card + B.card.choose 2 := by
  classical
  let P : Finset (ℤ × ℤ) :=
    B.diag ∪ (B ×ˢ B).filter fun p => p.1 < p.2
  have hmem (p : ℤ × ℤ) (hp : p ∈ P) :
      p.1 ∈ B ∧ p.2 ∈ B ∧ p.1 ≤ p.2 := by
    simp only [P, Finset.mem_union, Finset.mem_diag, Finset.mem_filter,
      Finset.mem_product] at hp
    rcases hp with hp | hp
    · exact ⟨hp.1, hp.2 ▸ hp.1, hp.2.le⟩
    · exact ⟨hp.1.1, hp.1.2, hp.2.le⟩
  have hdisj :
      Disjoint B.diag ((B ×ˢ B).filter fun p => p.1 < p.2) := by
    simp [Finset.disjoint_left]
  have hcard : P.card = B.card + B.card.choose 2 := by
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
  have hsubset : P.image f ⊆ B + B := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨hp₁, hp₂, -⟩ := hmem p hp
    exact Finset.add_mem_add hp₁ hp₂
  have hsupset : B + B ⊆ P.image f := by
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
  have heq : P.image f = B + B :=
    Finset.Subset.antisymm hsubset hsupset
  calc
    (B + B).card = (P.image f).card := congrArg Finset.card heq.symm
    _ = P.card := himage
    _ = B.card + B.card.choose 2 := hcard

private theorem sidon_subset_bridge
    (A B : Finset ℤ) (hBA : B ⊆ A)
    (hSidon :
      ∀ a ∈ B, ∀ b ∈ B, a ≤ b →
        ∀ c ∈ B, ∀ d ∈ B, c ≤ d →
          a + b = c + d → a = c ∧ b = d) :
    B.card * (B.card + 1) ≤
      2 * max (A + A).card (A * A).card := by
  have hsum := sidon_sumset_card B hSidon
  have hsum_mono : (B + B).card ≤ (A + A).card :=
    Finset.card_le_card (Finset.add_subset_add hBA hBA)
  have hmax : (B + B).card ≤ max (A + A).card (A * A).card :=
    hsum_mono.trans (Nat.le_max_left _ _)
  calc
    B.card * (B.card + 1) = 2 * (B.card + B.card.choose 2) :=
      (two_mul_card_add_choose_two B.card).symm
    _ = 2 * (B + B).card := by rw [hsum]
    _ ≤ 2 * max (A + A).card (A * A).card :=
      Nat.mul_le_mul_left 2 hmax

/--
Any finite integer set whose sum-product maximum is below the `|A|⁴ / K`
threshold has only correspondingly small Sidon subsets and simultaneously
has additive and multiplicative energy greater than `K`.
-/
theorem proof :
    ∀ (A : Finset ℤ) (K : ℕ),
      K * max (A + A).card (A * A).card < A.card ^ 4 →
        (∀ B : Finset ℤ, B ⊆ A →
          (∀ a ∈ B, ∀ b ∈ B, a ≤ b →
            ∀ c ∈ B, ∀ d ∈ B, c ≤ d →
              a + b = c + d → a = c ∧ b = d) →
          K * (B.card * (B.card + 1)) < 2 * A.card ^ 4) ∧
        K < Finset.addEnergy A A ∧
        K < Finset.mulEnergy A A := by
  intro A K hsmall
  have hadd : A.card ^ 4 ≤ (A + A).card * Finset.addEnergy A A := by
    simpa [← pow_add] using Finset.le_card_add_mul_addEnergy A A
  have hmul : A.card ^ 4 ≤ (A * A).card * Finset.mulEnergy A A := by
    simpa [← pow_add] using Finset.le_card_mul_mul_mulEnergy A A
  constructor
  · intro B hBA hSidon
    have hbridge := sidon_subset_bridge A B hBA hSidon
    calc
      K * (B.card * (B.card + 1)) ≤
          K * (2 * max (A + A).card (A * A).card) :=
        Nat.mul_le_mul_left K hbridge
      _ = 2 * (K * max (A + A).card (A * A).card) := by
        simp [Nat.mul_left_comm]
      _ < 2 * A.card ^ 4 :=
        Nat.mul_lt_mul_of_pos_left hsmall (by omega)
  · constructor
    · by_contra hn
      have henergy : Finset.addEnergy A A ≤ K := Nat.le_of_not_gt hn
      have hbound :
          (A + A).card * Finset.addEnergy A A ≤
            K * max (A + A).card (A * A).card := by
        calc
          (A + A).card * Finset.addEnergy A A ≤ (A + A).card * K :=
            Nat.mul_le_mul_left _ henergy
          _ ≤ max (A + A).card (A * A).card * K :=
            Nat.mul_le_mul_right _ (Nat.le_max_left _ _)
          _ = K * max (A + A).card (A * A).card := Nat.mul_comm _ _
      exact (Nat.not_le_of_lt hsmall) (hadd.trans hbound)
    · by_contra hn
      have henergy : Finset.mulEnergy A A ≤ K := Nat.le_of_not_gt hn
      have hbound :
          (A * A).card * Finset.mulEnergy A A ≤
            K * max (A + A).card (A * A).card := by
        calc
          (A * A).card * Finset.mulEnergy A A ≤ (A * A).card * K :=
            Nat.mul_le_mul_left _ henergy
          _ ≤ max (A + A).card (A * A).card * K :=
            Nat.mul_le_mul_right _ (Nat.le_max_right _ _)
          _ = K * max (A + A).card (A * A).card := Nat.mul_comm _ _
      exact (Nat.not_le_of_lt hsmall) (hmul.trans hbound)

end Submissions.Erdos52SidonEnergyObstruction.P29

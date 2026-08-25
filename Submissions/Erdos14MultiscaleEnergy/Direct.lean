import Mathlib

namespace Submissions.Erdos14MultiscaleEnergy.Direct

open scoped BigOperators

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

noncomputable def upperBlock (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (M + 1) (2 * M)).filter fun a => a ∈ A

noncomputable def repCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  let B := initialSegment A M
  exact ((B ×ˢ B).filter fun p => p.1 + p.2 = n).card

noncomputable def additiveEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.range (2 * M + 1), (repCount A M n) ^ 2

noncomputable def crossPairs (A : Set ℕ) (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  exact (B ×ˢ C) ∪ (C ×ˢ B)

noncomputable def crossRepCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  exact ((crossPairs A M).filter fun p => p.1 + p.2 = n).card

noncomputable def crossEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.Icc (M + 1) (3 * M), (crossRepCount A M n) ^ 2

lemma initial_double_eq_union (A : Set ℕ) (M : ℕ) :
    initialSegment A (2 * M) = initialSegment A M ∪ upperBlock A M := by
  classical
  ext a
  simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨_, ha2⟩, haA⟩
    by_cases haM : a ≤ M
    · exact Or.inl ⟨⟨by omega, haM⟩, haA⟩
    · exact Or.inr ⟨⟨by omega, ha2⟩, haA⟩
  · rintro (⟨⟨_, haM⟩, haA⟩ | ⟨⟨_, ha2⟩, haA⟩)
    · exact ⟨⟨by omega, by omega⟩, haA⟩
    · exact ⟨⟨by omega, ha2⟩, haA⟩

lemma blocks_disjoint (A : Set ℕ) (M : ℕ) :
    Disjoint (initialSegment A M) (upperBlock A M) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at ha hb
  omega

lemma crossPairs_card (A : Set ℕ) (M : ℕ) :
    (crossPairs A M).card =
      2 * (initialSegment A M).card * (upperBlock A M).card := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  have hBC : Disjoint B C := blocks_disjoint A M
  have hprod : Disjoint (B ×ˢ C) (C ×ˢ B) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_product] at hp hq
    exact (Finset.disjoint_left.mp hBC hp.1 hq.1).elim
  unfold crossPairs
  dsimp only
  rw [Finset.card_union_of_disjoint hprod]
  simp only [Finset.card_product]
  ring

lemma crossPairs_sum_mem (A : Set ℕ) (M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ crossPairs A M) :
    p.1 + p.2 ∈ Finset.Icc (M + 1) (3 * M) := by
  classical
  simp only [crossPairs, Finset.mem_union, Finset.mem_product] at hp
  simp only [Finset.mem_Icc]
  rcases hp with hp | hp
  · have hp₁ := hp.1
    have hp₂ := hp.2
    simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
    omega
  · have hp₁ := hp.1
    have hp₂ := hp.2
    simp only [initialSegment, upperBlock, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
    omega

lemma rep_add_cross_le (A : Set ℕ) (M n : ℕ) :
    repCount A M n + crossRepCount A M n ≤ repCount A (2 * M) n := by
  classical
  let B := initialSegment A M
  let C := upperBlock A M
  let D := initialSegment A (2 * M)
  let P₀ := B ×ˢ B
  let Pₓ := (B ×ˢ C) ∪ (C ×ˢ B)
  let P₂ := D ×ˢ D
  let F₀ := P₀.filter fun p => p.1 + p.2 = n
  let Fₓ := Pₓ.filter fun p => p.1 + p.2 = n
  let F₂ := P₂.filter fun p => p.1 + p.2 = n
  have hBD : B ⊆ D := by
    intro a ha
    simp only [B, D, initialSegment, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    exact ⟨⟨by omega, by omega⟩, ha.2⟩
  have hCD : C ⊆ D := by
    intro a ha
    simp only [C, D, upperBlock, initialSegment, Finset.mem_filter, Finset.mem_Icc] at ha ⊢
    exact ⟨⟨by omega, ha.1.2⟩, ha.2⟩
  have hdisj : Disjoint F₀ Fₓ := by
    rw [Finset.disjoint_left]
    intro p hp₀ hpₓ
    simp only [F₀, Fₓ, Finset.mem_filter, P₀, Pₓ, Finset.mem_product,
      Finset.mem_union] at hp₀ hpₓ
    have hBC : Disjoint B C := blocks_disjoint A M
    rcases hpₓ.1 with hpₓ | hpₓ
    · exact (Finset.disjoint_left.mp hBC hp₀.1.2 hpₓ.2).elim
    · exact (Finset.disjoint_left.mp hBC hp₀.1.1 hpₓ.1).elim
  have hsub : F₀ ∪ Fₓ ⊆ F₂ := by
    intro p hp
    simp only [Finset.mem_union] at hp
    simp only [F₂, Finset.mem_filter, P₂, Finset.mem_product]
    rcases hp with hp | hp
    · simp only [F₀, Finset.mem_filter, P₀, Finset.mem_product] at hp
      exact ⟨⟨hBD hp.1.1, hBD hp.1.2⟩, hp.2⟩
    · simp only [Fₓ, Finset.mem_filter, Pₓ, Finset.mem_union,
        Finset.mem_product] at hp
      refine ⟨?_, hp.2⟩
      rcases hp.1 with hp | hp
      · exact ⟨hBD hp.1, hCD hp.2⟩
      · exact ⟨hCD hp.1, hBD hp.2⟩
  change F₀.card + Fₓ.card ≤ F₂.card
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

lemma repCount_eq_zero_of_sum_gt (A : Set ℕ) (M n : ℕ) (hn : 2 * M < n) :
    repCount A M n = 0 := by
  classical
  rw [repCount]
  apply Finset.card_eq_zero.mpr
  ext p
  simp only [Finset.notMem_empty, iff_false, Finset.mem_filter,
    Finset.mem_product, initialSegment, Finset.mem_Icc]
  omega

lemma crossRepCount_eq_zero_of_not_mem (A : Set ℕ) (M n : ℕ)
    (hn : n ∉ Finset.Icc (M + 1) (3 * M)) :
    crossRepCount A M n = 0 := by
  classical
  rw [crossRepCount]
  apply Finset.card_eq_zero.mpr
  ext p
  simp only [Finset.notMem_empty, iff_false, Finset.mem_filter]
  intro hp
  exact hn (hp.2 ▸ crossPairs_sum_mem A M hp.1)

lemma cross_mass (A : Set ℕ) (M : ℕ) :
    ∑ n ∈ Finset.Icc (M + 1) (3 * M), crossRepCount A M n =
      2 * (initialSegment A M).card * (upperBlock A M).card := by
  classical
  let T := Finset.Icc (M + 1) (3 * M)
  have hmap : (crossPairs A M : Set (ℕ × ℕ)).MapsTo
      (fun p => p.1 + p.2) T := by
    intro p hp
    exact crossPairs_sum_mem A M hp
  rw [← crossPairs_card A M]
  simpa [crossRepCount, T] using (Finset.card_eq_sum_card_fiberwise hmap).symm

theorem proof :
    ∀ (A : Set ℕ) (M : ℕ),
      additiveEnergy A M + crossEnergy A M ≤ additiveEnergy A (2 * M) ∧
      4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 ≤
        2 * M * crossEnergy A M := by
  intro A M
  classical
  constructor
  · let S := Finset.range (4 * M + 1)
    let S₀ := Finset.range (2 * M + 1)
    let T := Finset.Icc (M + 1) (3 * M)
    let r := repCount A M
    let c := crossRepCount A M
    let R := repCount A (2 * M)
    have hpoint (n : ℕ) : r n ^ 2 + c n ^ 2 ≤ R n ^ 2 := by
      have h := rep_add_cross_le A M n
      dsimp only [r, c, R]
      nlinarith
    have hS₀S : S₀ ⊆ S := by
      intro n hn
      simp only [S₀, S, Finset.mem_range] at hn ⊢
      omega
    have hTS : T ⊆ S := by
      intro n hn
      simp only [T, Finset.mem_Icc, S, Finset.mem_range] at hn ⊢
      omega
    have hr_extend : (∑ n ∈ S, r n ^ 2) = ∑ n ∈ S₀, r n ^ 2 := by
      symm
      apply Finset.sum_subset hS₀S
      intro n hnS hnS₀
      have hn : 2 * M < n := by
        simp only [S, Finset.mem_range] at hnS
        simp only [S₀, Finset.mem_range] at hnS₀
        omega
      simp [r, repCount_eq_zero_of_sum_gt A M n hn]
    have hc_extend : (∑ n ∈ S, c n ^ 2) = ∑ n ∈ T, c n ^ 2 := by
      symm
      apply Finset.sum_subset hTS
      intro n hnS hnT
      simp [c, crossRepCount_eq_zero_of_not_mem A M n hnT]
    have hfinal : (∑ n ∈ S₀, r n ^ 2) + (∑ n ∈ T, c n ^ 2) ≤
        ∑ n ∈ S, R n ^ 2 := by
      rw [← hr_extend, ← hc_extend, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun n _ => hpoint n
    simp only [additiveEnergy, crossEnergy]
    dsimp only [S, S₀, T, r, c, R] at hfinal
    rw [show 2 * (2 * M) + 1 = 4 * M + 1 by omega]
    exact hfinal
  · let T := Finset.Icc (M + 1) (3 * M)
    let c := crossRepCount A M
    have hcard : T.card = 2 * M := by
      simp [T]
      omega
    have hmass : ∑ n ∈ T, c n =
        2 * (initialSegment A M).card * (upperBlock A M).card := by
      simpa [T, c] using cross_mass A M
    have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := c)
    change 4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 ≤
      2 * M * ∑ n ∈ T, c n ^ 2
    calc
      4 * ((initialSegment A M).card * (upperBlock A M).card) ^ 2 =
          (2 * (initialSegment A M).card * (upperBlock A M).card) ^ 2 := by ring
      _ = (∑ n ∈ T, c n) ^ 2 := by rw [hmass]
      _ ≤ T.card * ∑ n ∈ T, c n ^ 2 := hcs
      _ = 2 * M * ∑ n ∈ T, c n ^ 2 := by rw [hcard]

end Submissions.Erdos14MultiscaleEnergy.Direct

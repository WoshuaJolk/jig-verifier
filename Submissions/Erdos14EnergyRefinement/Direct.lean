import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos14EnergyRefinement.Direct

open scoped BigOperators

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionNat (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n => n ∉ uniquePairSums A).card

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 0 M).filter fun a => a ∈ A

noncomputable def repCount (A : Set ℕ) (M n : ℕ) : ℕ := by
  classical
  let B := initialSegment A M
  exact ((B ×ˢ B).filter fun p => p.1 + p.2 = n).card

noncomputable def additiveEnergy (A : Set ℕ) (M : ℕ) : ℕ := by
  classical
  exact ∑ n ∈ Finset.range (2 * M + 1), (repCount A M n) ^ 2

lemma unique_representations {A : Set ℕ} {n a b c d : ℕ}
    (hn : n ∈ uniquePairSums A)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a + b = n)
    (hc : c ∈ A) (hd : d ∈ A) (hcd : c + d = n) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hn with ⟨p, hp₁, hp₂, hp, hunique⟩
  have h₁ := hunique a ha b hb hab
  have h₂ := hunique c hc d hd hcd
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp_all

lemma repCount_le_card (A : Set ℕ) (M n : ℕ) :
    repCount A M n ≤ (initialSegment A M).card := by
  classical
  let B := initialSegment A M
  let F := (B ×ˢ B).filter fun p => p.1 + p.2 = n
  change F.card ≤ B.card
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
  · intro p hp
    change p ∈ F at hp
    simp only [F, Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  · intro p hp q hq hpq
    change p ∈ F at hp
    change q ∈ F at hq
    change p.1 = q.1 at hpq
    simp only [F, Finset.mem_filter, Finset.mem_product] at hp hq
    apply Prod.ext
    · exact hpq
    · omega

lemma repCount_zero_le_one (A : Set ℕ) (M : ℕ) :
    repCount A M 0 ≤ 1 := by
  classical
  let B := initialSegment A M
  let F := (B ×ˢ B).filter fun p => p.1 + p.2 = 0
  change F.card ≤ 1
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  change p ∈ F at hp
  change q ∈ F at hq
  simp only [F, Finset.mem_filter, Finset.mem_product] at hp hq
  apply Prod.ext <;> omega

lemma repCount_le_two_of_unique {A : Set ℕ} {M n : ℕ}
    (hn : n ∈ uniquePairSums A) :
    repCount A M n ≤ 2 := by
  classical
  let B := initialSegment A M
  let F := (B ×ˢ B).filter fun p => p.1 + p.2 = n
  let L := F.filter fun p => p.1 ≤ p.2
  let R := F.filter fun p => p.2 < p.1
  have hL : L.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro p q hp hq
    change p ∈ L at hp
    change q ∈ L at hq
    simp only [L, F, Finset.mem_filter, Finset.mem_product] at hp hq
    have hp₁ := hp.1.1.1
    have hp₂ := hp.1.1.2
    have hq₁ := hq.1.1.1
    have hq₂ := hq.1.1.2
    simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂ hq₁ hq₂
    have hu := unique_representations hn hp₁.2 hp₂.2 hp.1.2
      hq₁.2 hq₂.2 hq.1.2
    rcases hu with hu | hu
    · exact Prod.ext hu.1 hu.2
    · apply Prod.ext <;> omega
  have hR : R.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro p q hp hq
    change p ∈ R at hp
    change q ∈ R at hq
    simp only [R, F, Finset.mem_filter, Finset.mem_product] at hp hq
    have hp₁ := hp.1.1.1
    have hp₂ := hp.1.1.2
    have hq₁ := hq.1.1.1
    have hq₂ := hq.1.1.2
    simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂ hq₁ hq₂
    have hu := unique_representations hn hp₁.2 hp₂.2 hp.1.2
      hq₁.2 hq₂.2 hq.1.2
    rcases hu with hu | hu
    · exact Prod.ext hu.1 hu.2
    · omega
  have hsplit : L.card + R.card = F.card := by
    simpa [L, R, Nat.not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := F) (fun p : ℕ × ℕ => p.1 ≤ p.2))
  change F.card ≤ 2
  omega

theorem proof :
    ∀ (A : Set ℕ) (M : ℕ),
      let B := initialSegment A M
      let E := exceptionNat A (2 * M)
      additiveEnergy A M + 4 * E ≤ 8 * M + 1 + B.card ^ 2 * E := by
  intro A M
  classical
  let B := initialSegment A M
  let S := Finset.range (2 * M + 1)
  let T := Finset.Icc 1 (2 * M)
  let E := (Finset.Icc 1 (2 * M)).filter fun n => n ∉ uniquePairSums A
  let f := fun n => (repCount A M n) ^ 2
  have hET : E ⊆ T := by
    intro n hn
    simp only [E, Finset.mem_filter, Finset.mem_Icc] at hn
    simpa only [T, Finset.mem_Icc] using hn.1
  have hnon (n : ℕ) (hnT : n ∈ T) (hnE : n ∉ E) : f n ≤ 4 := by
    have hnrange : 1 ≤ n ∧ n ≤ 2 * M := by
      simpa only [T, Finset.mem_Icc] using hnT
    have hnu : n ∈ uniquePairSums A := by
      by_contra hbad
      exact hnE (by simp [E, hnrange.1, hnrange.2, hbad])
    have h := repCount_le_two_of_unique (M := M) hnu
    dsimp only [f]
    nlinarith
  have hexc (n : ℕ) (hnE : n ∈ E) : f n ≤ B.card ^ 2 := by
    have h := repCount_le_card A M n
    dsimp only [f, B]
    nlinarith
  have hzero : f 0 ≤ 1 := by
    have h := repCount_zero_le_one A M
    dsimp only [f]
    nlinarith
  have hsum_non :
      ∑ n ∈ T \ E, f n ≤ (T \ E).card * 4 := by
    calc
      ∑ n ∈ T \ E, f n ≤ ∑ _n ∈ T \ E, 4 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hnon n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2
      _ = (T \ E).card * 4 := by simp
  have hsum_exc :
      ∑ n ∈ E, f n ≤ E.card * B.card ^ 2 := by
    calc
      ∑ n ∈ E, f n ≤ ∑ _n ∈ E, B.card ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact hexc n hn
      _ = E.card * B.card ^ 2 := by simp
  have hsplit :
      (∑ n ∈ T \ E, f n) + ∑ n ∈ E, f n = ∑ n ∈ T, f n :=
    Finset.sum_sdiff hET
  have hcard : (T \ E).card + E.card = T.card :=
    Finset.card_sdiff_add_card_eq_card hET
  have hTcard : T.card = 2 * M := by simp [T]
  have hSdecomp : S = insert 0 T := by
    ext n
    simp only [S, T, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsumS : (∑ n ∈ S, f n) = f 0 + ∑ n ∈ T, f n := by
    rw [hSdecomp]
    simp [T]
  have hEcard : E.card = exceptionNat A (2 * M) := by
    simp [E, exceptionNat]
  dsimp only
  change (∑ n ∈ S, f n) + 4 * exceptionNat A (2 * M) ≤
    8 * M + 1 + B.card ^ 2 * exceptionNat A (2 * M)
  rw [← hEcard]
  calc
    (∑ n ∈ S, f n) + 4 * E.card =
        (f 0 + ((∑ n ∈ T \ E, f n) + ∑ n ∈ E, f n)) + 4 * E.card := by
          rw [hsumS, hsplit]
    _ ≤ (1 + ((T \ E).card * 4 + E.card * B.card ^ 2)) + 4 * E.card :=
      Nat.add_le_add
        (Nat.add_le_add hzero (Nat.add_le_add hsum_non hsum_exc))
        (Nat.le_refl _)
    _ = 1 + 4 * T.card + B.card ^ 2 * E.card := by
      rw [← hcard]
      ring
    _ = 8 * M + 1 + B.card ^ 2 * E.card := by
      rw [hTcard]
      omega

end Submissions.Erdos14EnergyRefinement.Direct

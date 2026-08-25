import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Submissions.Erdos14DensityTradeoff.Direct

def uniquePairSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧
    ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ + a₂ = n →
      (a₁ = p.1 ∧ a₂ = p.2) ∨ (a₁ = p.2 ∧ a₂ = p.1)}

noncomputable def exceptionNat (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter fun n => n ∉ uniquePairSums A).card

noncomputable def initialSegment (A : Set ℕ) (M : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 0 M).filter fun a => a ∈ A

lemma unique_representations {A : Set ℕ} {n a b c d : ℕ}
    (hn : n ∈ uniquePairSums A)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a + b = n)
    (hc : c ∈ A) (hd : d ∈ A) (hcd : c + d = n) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hn with ⟨p, hp₁, hp₂, hp, hunique⟩
  have h₁ := hunique a ha b hb hab
  have h₂ := hunique c hc d hd hcd
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp_all

lemma zero_unique {A : Set ℕ} (h0 : 0 ∈ A) : 0 ∈ uniquePairSums A := by
  refine ⟨(0, 0), h0, h0, rfl, ?_⟩
  intro a₁ ha₁ a₂ ha₂ hs
  left
  omega

theorem proof :
    ∀ (A : Set ℕ) (M : ℕ),
      let k := (initialSegment A M).card
      k * k ≤ 2 * (2 * M + 1) + k * exceptionNat A (2 * M) := by
  intro A M
  classical
  let B := initialSegment A M
  let P := B ×ˢ B
  let U := P.filter fun p => p.1 + p.2 ∈ uniquePairSums A
  let D := P.filter fun p => p.1 + p.2 ∉ uniquePairSums A
  let L := U.filter fun p => p.1 ≤ p.2
  let R := U.filter fun p => p.2 < p.1
  let S := Finset.range (2 * M + 1)
  let E := (Finset.Icc 1 (2 * M)).filter fun n => n ∉ uniquePairSums A

  have hL : L.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + p.2)
    · intro p hp
      change p ∈ L at hp
      simp only [L, U, Finset.mem_filter] at hp
      change p.1 + p.2 ∈ S
      simp only [S, Finset.mem_range]
      have hpP := hp.1.1
      simp only [P, Finset.mem_product] at hpP
      have hp₁ := hpP.1
      have hp₂ := hpP.2
      simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      omega
    · intro p hp q hq hpq
      change p ∈ L at hp
      change q ∈ L at hq
      simp only [L, U, Finset.mem_filter] at hp hq
      have hpP := hp.1.1
      have hqP := hq.1.1
      simp only [P, Finset.mem_product] at hpP hqP
      have hp₁ := hpP.1
      have hp₂ := hpP.2
      have hq₁ := hqP.1
      have hq₂ := hqP.2
      simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂ hq₁ hq₂
      have hu := unique_representations hp.1.2 hp₁.2 hp₂.2 rfl
        hq₁.2 hq₂.2 hpq.symm
      rcases hu with hu | hu
      · exact Prod.ext hu.1 hu.2
      · apply Prod.ext <;> omega

  have hR : R.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + p.2)
    · intro p hp
      change p ∈ R at hp
      simp only [R, U, Finset.mem_filter] at hp
      change p.1 + p.2 ∈ S
      simp only [S, Finset.mem_range]
      have hpP := hp.1.1
      simp only [P, Finset.mem_product] at hpP
      have hp₁ := hpP.1
      have hp₂ := hpP.2
      simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      omega
    · intro p hp q hq hpq
      change p ∈ R at hp
      change q ∈ R at hq
      simp only [R, U, Finset.mem_filter] at hp hq
      have hpP := hp.1.1
      have hqP := hq.1.1
      simp only [P, Finset.mem_product] at hpP hqP
      have hp₁ := hpP.1
      have hp₂ := hpP.2
      have hq₁ := hqP.1
      have hq₂ := hqP.2
      simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂ hq₁ hq₂
      have hu := unique_representations hp.1.2 hp₁.2 hp₂.2 rfl
        hq₁.2 hq₂.2 hpq.symm
      rcases hu with hu | hu
      · exact Prod.ext hu.1 hu.2
      · omega

  have hD : D.card ≤ (B ×ˢ E).card := by
    apply Finset.card_le_card_of_injOn
      (fun p : ℕ × ℕ => (p.1, p.1 + p.2))
    · intro p hp
      change p ∈ D at hp
      simp only [D, Finset.mem_filter] at hp
      change (p.1, p.1 + p.2) ∈ B ×ˢ E
      simp only [Finset.mem_product]
      have hpP := hp.1
      simp only [P, Finset.mem_product] at hpP
      refine ⟨hpP.1, ?_⟩
      simp only [E, Finset.mem_filter, Finset.mem_Icc]
      have hp₁ := hpP.1
      have hp₂ := hpP.2
      simp only [B, initialSegment, Finset.mem_filter, Finset.mem_Icc] at hp₁ hp₂
      refine ⟨⟨?_, by omega⟩, hp.2⟩
      by_contra hz
      have hzsum : p.1 + p.2 = 0 := by omega
      have hpzero : p.1 = 0 := by omega
      exact hp.2 (by simpa [hzsum] using zero_unique (by simpa [hpzero] using hp₁.2))
    · intro p hp q hq hpq
      change p ∈ D at hp
      change q ∈ D at hq
      simp only [Prod.mk.injEq] at hpq
      apply Prod.ext
      · exact hpq.1
      · omega

  have hPU : U.card + D.card = P.card := by
    simpa [U, D] using
      (Finset.card_filter_add_card_filter_not
        (s := P) (fun p : ℕ × ℕ => p.1 + p.2 ∈ uniquePairSums A))
  have hUL : L.card + R.card = U.card := by
    simpa [L, R, Nat.not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := U) (fun p : ℕ × ℕ => p.1 ≤ p.2))
  have hScard : S.card = 2 * M + 1 := by simp [S]
  have hEcard : E.card = exceptionNat A (2 * M) := by
    simp [E, exceptionNat]
  have hPcard : P.card = B.card * B.card := by simp [P]
  have hBEcard : (B ×ˢ E).card = B.card * E.card := by simp
  dsimp only
  change B.card * B.card ≤
    2 * (2 * M + 1) + B.card * exceptionNat A (2 * M)
  rw [hScard] at hL hR
  rw [hBEcard, hEcard] at hD
  calc
    B.card * B.card = P.card := hPcard.symm
    _ = U.card + D.card := hPU.symm
    _ = (L.card + R.card) + D.card := by rw [hUL]
    _ ≤ ((2 * M + 1) + (2 * M + 1)) +
        B.card * exceptionNat A (2 * M) :=
      Nat.add_le_add (Nat.add_le_add hL hR) hD
    _ = 2 * (2 * M + 1) + B.card * exceptionNat A (2 * M) := by omega

end Submissions.Erdos14DensityTradeoff.Direct

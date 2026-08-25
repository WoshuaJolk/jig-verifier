import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Submissions.Erdos10DistinctNormalization.CarryProof

abbrev represented (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

abbrev representedDistinct (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.Nodup ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

private def sumPowers (s : Multiset ℕ) : ℕ :=
  (s.map (fun e => (2 : ℕ) ^ e)).sum

private theorem normalize (s : Multiset ℕ) :
    ∃ t : Multiset ℕ, t.Nodup ∧ t.card ≤ s.card ∧ sumPowers t = sumPowers s := by
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hs : s.Nodup
      · exact ⟨s, hs, hcard.le, rfl⟩
      · rw [Multiset.nodup_iff_count_le_one] at hs
        push Not at hs
        obtain ⟨e, he⟩ := hs
        have he_mem : e ∈ s := Multiset.count_pos.mp (by omega)
        have he_mem_erase : e ∈ s.erase e := Multiset.count_pos.mp (by
          rw [Multiset.count_erase_self]
          omega)
        let r := (s.erase e).erase e
        let s' := (e + 1) ::ₘ r
        have hr_card : r.card + 2 = s.card := by
          dsimp [r]
          have h₁ := Multiset.card_erase_add_one he_mem
          have h₂ := Multiset.card_erase_add_one he_mem_erase
          omega
        have hs'_card : s'.card < s.card := by
          simp only [s', Multiset.card_cons]
          omega
        obtain ⟨t, ht_nodup, ht_card, ht_sum⟩ :=
          ih s'.card (by omega) s' rfl
        refine ⟨t, ht_nodup, ?_, ?_⟩
        · simpa [hcard] using ht_card.trans hs'_card.le
        · rw [ht_sum]
          have hreconstruct : e ::ₘ e ::ₘ r = s := by
            dsimp [r]
            rw [Multiset.cons_erase he_mem_erase, Multiset.cons_erase he_mem]
          rw [← hreconstruct]
          simp [sumPowers, s', r, pow_succ]
          omega

theorem proof : ∀ k n : ℕ, represented k n ↔ representedDistinct k n := by
  intro k n
  constructor
  · rintro ⟨p, exponents, hp, hcard, hn⟩
    obtain ⟨normalized, hnodup, hcard', hsum⟩ := normalize exponents
    refine ⟨p, normalized, hp, hnodup, hcard'.trans hcard, ?_⟩
    calc
      n = p + sumPowers exponents := hn
      _ = p + sumPowers normalized := by rw [hsum]
  · rintro ⟨p, exponents, hp, _, hcard, hn⟩
    exact ⟨p, exponents, hp, hcard, hn⟩

end Submissions.Erdos10DistinctNormalization.CarryProof

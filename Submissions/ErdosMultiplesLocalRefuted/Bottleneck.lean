import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace Submissions.ErdosMultiplesLocalRefuted.Bottleneck

abbrev localClaim : Prop := ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ∃ f : ℕ → ℕ,
        (∀ k ∈ (Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k),
          ∃ a ∈ A, ∃ s : ℕ, a ∣ k ∧ f k = a * s ∧ 1 ≤ s ∧ a * s ≤ n ∧
            s * m ≤ (k / a) * n + m ∧ (k / a) * n ≤ s * m + m) ∧
        (∀ d : ℕ,
          n * (((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).filter
            (fun k => f k = d)).card < 2 * m)

/-- Three source points are forced onto 20, but its permitted load is at most two. -/
theorem proof : ¬ localClaim := by
  intro h
  obtain ⟨f, hf, hcap⟩ := h {4, 5} (by simp) (by simp) 23 32 (by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> decide) (by decide)
  have force28 : f 28 = 20 := by
    obtain ⟨a, ha, s, hd, heq, hs, hbound, hlo, hhi⟩ := hf 28 (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · norm_num at hlo hhi
      omega
    · norm_num at hd
  have force30 : f 30 = 20 := by
    obtain ⟨a, ha, s, hd, heq, hs, hbound, hlo, hhi⟩ := hf 30 (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · norm_num at hd
    · norm_num at hlo hhi
      omega
  have force32 : f 32 = 20 := by
    obtain ⟨a, ha, s, hd, heq, hs, hbound, hlo, hhi⟩ := hf 32 (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · norm_num at hlo hhi
      omega
    · norm_num at hd
  have subset : ({28, 30, 32} : Finset ℕ) ⊆
      (((Finset.Icc 1 32).filter (fun k => ∃ a ∈ ({4, 5} : Finset ℕ), a ∣ k)).filter
        (fun k => f k = 20)) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · norm_num [force28]
    · norm_num [force30]
    · norm_num [force32]
  have hc := Finset.card_le_card subset
  have hsmall := hcap 20
  norm_num at hc hsmall
  omega

/-- The original density inequality is true at this obstruction. -/
theorem original_inequality_control :
    23 * ((Finset.Icc 1 32).filter
      (fun k => ∃ a ∈ ({4, 5} : Finset ℕ), a ∣ k)).card <
    2 * 32 * ((Finset.Icc 1 23).filter
      (fun k => ∃ a ∈ ({4, 5} : Finset ℕ), a ∣ k)).card := by decide

end Submissions.ErdosMultiplesLocalRefuted.Bottleneck

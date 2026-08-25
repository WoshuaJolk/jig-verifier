import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Submissions.Erdos39InfiniteSidonPowers3.Worker03Powers3

lemma three_not_dvd_one_add_pow (n : ℕ) : ¬ 3 ∣ 1 + 3 ^ n := by
  cases n with
  | zero => norm_num
  | succ n => simp [pow_succ, Nat.dvd_iff_mod_eq_zero]

lemma factorization_three_add_pow {i j : ℕ} (hij : i ≤ j) :
    (3 ^ i + 3 ^ j).factorization 3 = i := by
  have hfac : 3 ^ i + 3 ^ j = 3 ^ i * (1 + 3 ^ (j - i)) := by
    rw [← Nat.pow_sub_mul_pow 3 hij]
    ring
  rw [hfac, Nat.factorization_mul (by positivity) (by positivity),
    Nat.Prime.factorization_pow (by decide), Finsupp.add_apply,
    Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (three_not_dvd_one_add_pow (j - i))]
  simp

lemma pow_three_add_pow_three_unique (a b c d : ℕ)
    (h : 3 ^ a + 3 ^ c = 3 ^ b + 3 ^ d) :
    (a = b ∧ c = d) ∨ (a = d ∧ c = b) := by
  have hinj : Function.Injective (fun n : ℕ ↦ 3 ^ n) :=
    Nat.pow_right_injective (by decide)
  by_cases hac : a ≤ c
  · by_cases hbd : b ≤ d
    · have hab : a = b := by
        rw [← factorization_three_add_pow hac, h, factorization_three_add_pow hbd]
      left
      refine ⟨hab, hinj ?_⟩
      exact Nat.add_left_cancel (hab ▸ h)
    · have hdb : d ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbd)
      have had : a = d := by
        rw [← factorization_three_add_pow hac, h, add_comm,
          factorization_three_add_pow hdb]
      right
      refine ⟨had, hinj ?_⟩
      exact Nat.add_left_cancel (had ▸ h.trans (add_comm _ _))
  · have hca : c ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hac)
    by_cases hbd : b ≤ d
    · have hcb : c = b := by
        rw [← factorization_three_add_pow hca, add_comm, h,
          factorization_three_add_pow hbd]
      right
      refine ⟨hinj ?_, hcb⟩
      apply Nat.add_left_cancel
      calc
        3 ^ b + 3 ^ a = 3 ^ a + 3 ^ b := add_comm _ _
        _ = 3 ^ b + 3 ^ d := hcb ▸ h
    · have hdb : d ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbd)
      have hcd : c = d := by
        rw [← factorization_three_add_pow hca, add_comm, h, add_comm,
          factorization_three_add_pow hdb]
      left
      refine ⟨hinj ?_, hcd⟩
      exact Nat.add_right_cancel (hcd ▸ h)

theorem proof :
    ∃ A : Set ℕ, A.Infinite ∧
      ∀ i₁ ∈ A, ∀ j₁ ∈ A, ∀ i₂ ∈ A, ∀ j₂ ∈ A,
        i₁ + i₂ = j₁ + j₂ →
          (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁) := by
  refine ⟨Set.range (fun n : ℕ ↦ 3 ^ n),
    Set.infinite_range_of_injective
      (Nat.pow_right_injective (by decide)), ?_⟩
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ _ ⟨d, rfl⟩ h
  rcases pow_three_add_pow_three_unique a b c d h with
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end Submissions.Erdos39InfiniteSidonPowers3.Worker03Powers3

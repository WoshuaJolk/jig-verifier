import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos342FirstTwinPairs.Direct

def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

theorem ulam_two (a : ℕ → ℕ) (h : IsUlamSequence a) : a 2 = 3 := by
  obtain ⟨ha0, ha1, ha⟩ := h
  obtain ⟨_, ⟨⟨i, j⟩, ⟨hij, hj, hsum⟩, _⟩, _⟩ := ha 2 (by omega)
  interval_cases j
  · omega
  · have hi : i = 0 := by omega
    subst hi
    simpa [ha0, ha1] using hsum

theorem ulam_three (a : ℕ → ℕ) (h : IsUlamSequence a) : a 3 = 4 := by
  obtain ⟨ha0, ha1, ha⟩ := h
  have ha2 := ulam_two a ⟨ha0, ha1, ha⟩
  obtain ⟨hinc, ⟨⟨i, j⟩, ⟨hij, hj, hsum⟩, _⟩, hmin⟩ :=
    ha 3 (by omega)
  interval_cases j
  · omega
  · have hi : i = 0 := by omega
    subst hi
    rw [ha0, ha1] at hsum
    rw [ha2] at hinc
    omega
  · interval_cases i
    · rw [ha0, ha2] at hsum
      exact hsum
    · rw [ha1, ha2] at hsum
      exfalso
      have h4 := hmin 4 (by rw [ha2]; omega) (by omega)
      apply h4
      refine ⟨⟨0, 2⟩, ⟨by omega, by omega, by rw [ha0, ha2]⟩, ?_⟩
      rintro ⟨i', j'⟩ ⟨hij', hj', hsum'⟩
      simp only [Prod.mk.injEq]
      interval_cases j'
      · omega
      · interval_cases i'
        rw [ha0, ha1] at hsum'
        omega
      · interval_cases i'
        · rw [ha0, ha2] at hsum'
          constructor <;> omega
        · rw [ha1, ha2] at hsum'
          omega

theorem proof :
    ∀ a : ℕ → ℕ, IsUlamSequence a →
      a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 3 ∧ a 3 = 4 ∧
      (∃ m, a m = a 0 + 2) ∧ (∃ m, a m = a 1 + 2) := by
  intro a h
  have ha0 := h.1
  have ha1 := h.2.1
  have ha2 := ulam_two a h
  have ha3 := ulam_three a h
  exact ⟨ha0, ha1, ha2, ha3, ⟨2, by omega⟩, ⟨3, by omega⟩⟩

end Submissions.Erdos342FirstTwinPairs.Direct

import Mathlib.Data.Int.ModEq

namespace Submissions.Erdos25FiniteLocalization.Worker01

def Survives (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) : Prop :=
  ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])

def SurvivesBefore (k : ℕ) (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) : Prop :=
  ∀ i < k, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])

theorem proof :
    ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), StrictMono seq_n →
      ∀ (k x : ℕ), x < seq_n k →
        (Survives seq_n seq_a x ↔ SurvivesBefore k seq_n seq_a x) := by
  intro seq_n seq_a hmono k x hx
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : i < k
    · exact h i hi
    · left
      have hki : k ≤ i := Nat.le_of_not_gt hi
      have hxi : x < seq_n i :=
        lt_of_lt_of_le hx (hmono.monotone hki)
      exact_mod_cast hxi

end Submissions.Erdos25FiniteLocalization.Worker01

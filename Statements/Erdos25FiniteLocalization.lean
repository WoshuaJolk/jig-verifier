import Mathlib.Data.Int.ModEq

namespace Statements.Erdos25FiniteLocalization

def Survives (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) : Prop :=
  ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])

def SurvivesBefore (k : ℕ) (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) : Prop :=
  ∀ i < k, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])

/-- Below the `k`th modulus, all later thresholded congruences are inactive. -/
abbrev statement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), StrictMono seq_n →
    ∀ (k x : ℕ), x < seq_n k →
      (Survives seq_n seq_a x ↔ SurvivesBefore k seq_n seq_a x)

theorem target : statement := sorry

end Statements.Erdos25FiniteLocalization

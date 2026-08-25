import Mathlib.Data.Finset.Basic

namespace Submissions.Erdos864ExceptionalSplit.FalsePremise

def PairUniqueExcept (A : Finset ℕ) (e : ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d → a + b ≠ e →
        a = c ∧ b = d

def PairUnique (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≤ b → c ≤ d → a + b = c + d →
        a = c ∧ b = d

theorem proof :
    False →
      ∀ (A : Finset ℕ) (e : ℕ),
        PairUniqueExcept A e →
          PairUnique (A.filter fun a => 2 * a ≤ e) ∧
            PairUnique (A.filter fun a => e < 2 * a) := by
  intro h
  exact h.elim

end Submissions.Erdos864ExceptionalSplit.FalsePremise

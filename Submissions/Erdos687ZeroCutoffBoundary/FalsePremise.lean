import Mathlib.Data.Nat.Prime.Basic

namespace Submissions.Erdos687ZeroCutoffBoundary.FalsePremise

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧
        m % p = residue p % p

theorem proof :
    False →
      ∀ y : ℕ, CoversInitialInterval 0 y ↔ y = 0 := by
  intro h
  exact h.elim

end Submissions.Erdos687ZeroCutoffBoundary.FalsePremise

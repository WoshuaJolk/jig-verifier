import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos687ZeroCutoffBoundary

def CoversInitialInterval (X y : ℕ) : Prop :=
  ∃ residue : ℕ → ℕ,
    ∀ m : ℕ, 1 ≤ m → m ≤ y →
      ∃ p : ℕ, p.Prime ∧ p ≤ X ∧
        m % p = residue p % p

abbrev statement : Prop :=
  ∀ y : ℕ, CoversInitialInterval 0 y ↔ y = 0

theorem target : statement := sorry

end Statements.Erdos687ZeroCutoffBoundary

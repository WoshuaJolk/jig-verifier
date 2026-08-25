import Mathlib.Data.Nat.GCD.Basic

/-!
# Absorbing a common factor into an aligned lattice
-/

namespace Statements.Erdos12CoreAbsorption

abbrev statement : Prop :=
  ∀ L r c q₀ : ℕ,
    Nat.Coprime L r →
    0 < c →
    c ∣ r + L * q₀ →
    Nat.Coprime c L ∧
      (∀ q, q₀ ≤ q → c ∣ r + L * q → c ∣ q - q₀) ∧
      ∃ d,
        r + L * q₀ = c * d ∧
        Nat.gcd (L * c) (r + L * q₀) = c ∧
        ∀ k, r + L * (q₀ + c * k) = c * (d + L * k)

theorem target : statement := sorry

end Statements.Erdos12CoreAbsorption

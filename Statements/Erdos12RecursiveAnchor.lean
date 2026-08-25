import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat

/-!
# Reflection after adjoining an aligned tail element

If an aligned progression has the form `r + L*q`, then a fresh element at
quotient `q` acts on later quotient indices with modulus
`(r + L*q) / gcd(L,r)`.
-/

namespace Statements.Erdos12RecursiveAnchor

abbrev statement : Prop :=
  ∀ (A : Set ℕ) (L r q : ℕ) (Q : Finset ℕ),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ∣ b + c → a < b → a < c → b = c) →
    0 < L →
    r + L * q ∈ A →
    (∀ s ∈ Q,
      r + L * s ∈ A ∧ q < s ∧
        s < q + (r + L * q) / Nat.gcd L r) →
    Q.card ≤ ((r + L * q) / Nat.gcd L r) / 2

theorem target : statement := sorry

end Statements.Erdos12RecursiveAnchor

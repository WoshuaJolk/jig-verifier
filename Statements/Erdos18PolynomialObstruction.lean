import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18PolynomialObstruction

/-- Every failure of divisibility by `k!` has an excessive prime-power
certificate larger than `k`; in the cubic range the certificate is itself at
most cubic. Such a certificate obstructs at most one member of a shorter shift
window. The final conjunct gives a genuine cubic-range gap at the base case. -/
abbrev statement : Prop :=
  (∀ k m : ℕ, 0 < m → ¬(m ∣ k.factorial) →
    ∃ p Q : ℕ,
      p.Prime ∧
      Q = p ^ (k.factorial.factorization p + 1) ∧
      k < Q ∧
      Q ∣ m ∧
      Q ≤ m) ∧
  (∀ Q A h s t : ℕ,
    h < Q →
    0 < s →
    s < t →
    t ≤ h →
    h < A →
    ¬(Q ∣ A - s ∧ Q ∣ A - t)) ∧
  (∀ k m : ℕ, 0 < m → m ≤ k ^ 3 → ¬(m ∣ k.factorial) →
    ∃ p Q : ℕ,
      p.Prime ∧
      Q = p ^ (k.factorial.factorization p + 1) ∧
      k < Q ∧
      Q ∣ m ∧
      Q ≤ k ^ 3) ∧
  (∀ m : ℕ, 181 ≤ m → m < 7 * 6 * 5 →
    ¬(m ∣ Nat.factorial 7))

theorem target : statement := sorry

end Statements.Erdos18PolynomialObstruction

import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18FiniteQuotientCoverage

/-- A quotient is covered when it is a sum of at most two distinct divisors of
the indicated factorial. -/
def quotientCovered (N q : ℕ) : Prop :=
  ∃ E : Finset ℕ,
    E ⊆ N.factorial.divisors ∧
    E.card ≤ 2 ∧
    q = E.sum id

/-- Distinct divisor pairs lift through one factorial radix, and uniform
two-divisor coverage of the finite quotient range implies four-to-three
compression for the next radix block. -/
abbrev statement : Prop :=
  (∀ n m q r x y : ℕ, 7 ≤ n →
    m = q * n + r →
    r < n →
    0 < x →
    0 < y →
    x ≠ y →
    q = x + y →
    x ∣ (n - 1).factorial →
    y ∣ (n - 1).factorial →
    ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧
      D.card ≤ 3 ∧
      m = D.sum id) ∧
  (∀ n m q r : ℕ, 7 ≤ n →
    m = q * n + r →
    r < n →
    quotientCovered (n - 1) q →
    ∃ D : Finset ℕ,
      D ⊆ n.factorial.divisors ∧
      D.card ≤ 3 ∧
      m = D.sum id) ∧
  (∀ n : ℕ, 7 ≤ n →
    (∀ q : ℕ,
      q < (n - 1) * (n - 2) * (n - 3) →
      quotientCovered (n - 1) q) →
    ∀ m : ℕ,
      m < n * (n - 1) * (n - 2) * (n - 3) →
      ∃ D : Finset ℕ,
        D ⊆ n.factorial.divisors ∧
        D.card ≤ 3 ∧
        m = D.sum id) ∧
  (∀ r : ℕ, r < 7 →
    ∃ D : Finset ℕ,
      D ⊆ (Nat.factorial 7).divisors ∧
      D.card ≤ 3 ∧
      59 * 7 + r = D.sum id)

theorem target : statement := sorry

end Statements.Erdos18FiniteQuotientCoverage

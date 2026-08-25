import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18MultiRescue

/-- The first summand in the nonlocal carry is tunable.  If
`q = k*v+y`, `q+v=w+t`, and `y+r+k*t=s+z`, then
`(k+1)q+r = s+k*w+z`.  A prime larger than a short interval can obstruct
at most one of its shifted correction candidates.  The last conjunct certifies
that two such rescue families cover every residue of the `n=29` model. -/
abbrev statement : Prop :=
  (∀ k q v y r s t w z : ℕ,
    6 ≤ k →
    q = k * v + y →
    q + v = w + t →
    y + r + k * t = s + z →
    0 < w →
    0 < s →
    0 < z →
    r < k + 1 →
    w ∣ (k - 1).factorial →
    s ∣ (k + 1).factorial →
    z ∣ (k + 1).factorial →
    s ≠ k * w →
    s ≠ z →
    k * w ≠ z →
    ∃ D : Finset ℕ,
      D ⊆ (k + 1).factorial.divisors ∧
      D.card ≤ 3 ∧
      (k + 1) * q + r = D.sum id) ∧
  (∀ p A h s t : ℕ,
    p.Prime →
    h < p →
    0 < s →
    s < t →
    t ≤ h →
    h < A →
    ¬(p ∣ A - s ∧ p ∣ A - t)) ∧
  (∀ r : ℕ, r < 29 →
    ∃ D : Finset ℕ,
      D ⊆ (Nat.factorial 29).divisors ∧
      D.card ≤ 3 ∧
      29 * 18191 + r = D.sum id) ∧
  (Nat.Prime 31 ∧ 31 ∣ 124 ∧
    Nat.Prime 41 ∧ 41 ∣ 123 ∧
    Nat.Prime 61 ∧ 61 ∣ 122 ∧
    96 ∣ Nat.factorial 29)

theorem target : statement := sorry

end Statements.Erdos18MultiRescue

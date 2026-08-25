import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

namespace Statements.Erdos18GridFailureRescue

/-- A failed grid cofactor `v` has an affine nonlocal replacement
`w = q + v - 1`.  The first branch is the original grid valuation test.
The second branch gives
`(k+1)q+r = (k+1) + k*w + z`, where `z = y+r-1`.
The final conjunct certifies the non-enumerative core of the `n=29` rescue:
`647` is replaced by the factorial divisor `18837`, leaving `74+r`. -/
abbrev statement : Prop :=
  (∀ k q v y w z r : ℕ,
    6 ≤ k →
    q = k * v + y →
    q + v = w + 1 →
    y + r = z + 1 →
    0 < v →
    0 < y →
    0 < w →
    0 < z →
    r < k + 1 →
    y ∣ k.factorial →
    (((∀ p : ℕ, p.Prime →
        v.factorization p ≤ (k - 1).factorial.factorization p) ∧
        k * v ≠ y) ∨
      ((∀ p : ℕ, p.Prime →
        w.factorization p ≤ (k - 1).factorial.factorization p) ∧
        (∀ p : ℕ, p.Prime →
          z.factorization p ≤ (k + 1).factorial.factorization p) ∧
        k + 1 ≠ k * w ∧
        k + 1 ≠ z ∧
        k * w ≠ z)) →
    ∃ D : Finset ℕ,
      D ⊆ (k + 1).factorial.divisors ∧
      D.card ≤ 3 ∧
      (k + 1) * q + r = D.sum id) ∧
  (18837 ∣ Nat.factorial 27 ∧
    28 * 18837 = 527436 ∧
    ∀ r : ℕ, r < 29 → 74 + r ∣ Nat.factorial 29 →
      let D : Finset ℕ := {29, 527436, 74 + r}
      D ⊆ (Nat.factorial 29).divisors ∧
        D.card = 3 ∧
        18191 * 29 + r = D.sum id)

theorem target : statement := sorry

end Statements.Erdos18GridFailureRescue

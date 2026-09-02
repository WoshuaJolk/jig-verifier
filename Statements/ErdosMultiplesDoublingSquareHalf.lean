import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingSquareHalf — the Square Bound for `A ⊆ (n/2, n]`

The half-range case of `ErdosMultiplesDoublingSquare`: if every `a ∈ A` satisfies
`n < 2a` and `a ≤ n`, then for all `m > n`

  `U(n)² · m ≤ U(m) · n²`.

Here `U(n) = n − |A|` (each generator has exactly one multiple in `[1, n]`, itself) and the
union bound `M(m) ≤ ∑ ⌊m/a⌋` reduces the claim to the sum inequality

  `∑_{a ∈ A} 1/a ≤ r (2n − r) / n²`,   `r = |A|`,

for `r` distinct integers in `(n/2, n]`, which holds because the `i`-th smallest is at
least `⌊n/2⌋ + i`. This is the regime where #488 itself is nearly sharp (`A = {a}`,
`n = 2a − 1`), so the Square Bound is not weaker than #488 there.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSquareHalf

/-- Square Bound when every generator lies in `(n/2, n]`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n ∧ n < 2 * a) → n < m →
      ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
        ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSquareHalf

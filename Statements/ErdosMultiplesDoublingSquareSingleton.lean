import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingSquareSingleton — the Square Bound for one generator

The case `A = {a}` of `ErdosMultiplesDoublingSquare`: for `1 ≤ a ≤ n < m`,

  `(n − ⌊n/a⌋)² · m ≤ (m − ⌊m/a⌋) · n²`.

Proof: `(2a − 1)⌊n/a⌋ ≥ n` gives `n − ⌊n/a⌋ ≤ n (2a−2)/(2a−1)`, and `a⌊m/a⌋ ≤ m` gives
`m − ⌊m/a⌋ ≥ m (a−1)/a`; then `4a(a−1) ≤ (2a−1)²`. Equality is approached at
`n = 2a − 1`, `m = 2a`, which is why the constant in the Square Bound cannot be improved.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSquareSingleton

/-- Square Bound for `A = {a}`. -/
abbrev statement : Prop :=
  ∀ a : ℕ, 0 < a → ∀ n m : ℕ, a ≤ n → n < m →
    ((Finset.Icc 1 n).filter (fun k => ¬ ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card ^ 2 * m ≤
      ((Finset.Icc 1 m).filter (fun k => ¬ ∃ b ∈ ({a} : Finset ℕ), b ∣ k)).card * n ^ 2

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSquareSingleton

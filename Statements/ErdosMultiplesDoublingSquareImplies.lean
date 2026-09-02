import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingSquareImplies — the Square Bound gives Erdős #488

If `U(n)² · m ≤ U(m) · n²` for all `A`, `m > n ≥ max A` (statement
`ErdosMultiplesDoublingSquare`, `U` = number of non-multiples), then with `M(x) = x − U(x)`

  `n² · M(m) ≤ 2nm · M(n) − m · M(n)² < 2nm · M(n)`,

since `M(n) ≥ 1`; dividing by `n` is Erdős #488, with the sharper constant `2 − M(n)/n`.
The hypothesis is restated inline (the verifier forbids importing `Statements.*`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSquareImplies

/-- Square Bound ⇒ `n · M(m) < 2m · M(n)` for all `m > n ≥ max A`. -/
abbrev statement : Prop :=
  (∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      ((Finset.Icc 1 n).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card ^ 2 * m ≤
        ((Finset.Icc 1 m).filter (fun k => ¬ ∃ a ∈ A, a ∣ k)).card * n ^ 2) →
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSquareImplies

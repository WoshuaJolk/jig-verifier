import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingHalf — Erdős #488 when every generator exceeds `n / 2`

The instance of `Statements.ErdosMultiplesDoubling.statement` in which `A ⊆ (n/2, n]`, for
`A` of any size. Same `Finset.filter` vocabulary as the parent statement.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingHalf

/-- For every nonempty finite `A` with `n < 2a ≤ 2n` for all `a ∈ A`, and every `m > n`,
`n * #{k ∈ [1,m] : ∃ a ∈ A, a ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ a ∈ A, a ∣ k}`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → ∀ n m : ℕ, (∀ a ∈ A, n < 2 * a ∧ a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingHalf

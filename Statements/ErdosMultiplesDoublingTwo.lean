import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingTwo — the two-generator case of Erdős #488

The instance `A = {a, b}` of `Statements.ErdosMultiplesDoubling.statement`, for all positive
`a ≠ b` and all `n ≥ max a b`, `m > n`. Written in the same `Finset.filter` vocabulary as the
parent statement with `A = {a, b}`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingTwo

/-- For all positive `a ≠ b`, every `n ≥ max a b` and every `m > n`,
`n * #{k ∈ [1,m] : a ∣ k ∨ b ∣ k} < 2 * m * #{k ∈ [1,n] : a ∣ k ∨ b ∣ k}`. -/
abbrev statement : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b → ∀ n m : ℕ, a ≤ n → b ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ c ∈ ({a, b} : Finset ℕ), c ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingTwo

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# ErdosMultiplesDoublingSparse — the union-bound criterion for Erdős #488

Writing `M x` for the number of multiples of `A` in `[1, x]`, the trivial bound
`M m ≤ ∑ a ∈ A, m / a` shows that the doubling inequality `n * M m < 2 * m * M n` holds for
every `m > n` as soon as `∑ a ∈ A, n / a < 2 * M n` (real division). This is the regime in
which the elements of `A` overlap little below `n`; it contains every singleton and every
`A ⊆ (n/2, n]`, and it needs no hypothesis on `A` at all.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingSparse

/-- If `∑ a ∈ A, n / a < 2 * M n` in `ℚ`, then `n * M m < 2 * m * M n` for every `m > n`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, ∀ n m : ℕ, n < m →
    (∑ a ∈ A, (n : ℚ) / a) <
      2 * (((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card : ℚ) →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingSparse

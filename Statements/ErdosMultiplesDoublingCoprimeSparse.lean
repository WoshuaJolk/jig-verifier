import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.GCD.Basic

/-!
# ErdosMultiplesDoublingCoprimeSparse — Erdős #488 for pairwise coprime sets with `min A > 2(|A|-1)`

The instance of `Statements.ErdosMultiplesDoubling.statement` for every pairwise coprime finite
`A ⊆ ℕ_{>0}` all of whose elements exceed `2 (|A| - 1)`, all `n ≥ max A` and all `m > n`.
Every such set is primitive; in particular the statement covers every set of `r` primes
each larger than `2 r - 2`, for every `r` (so arbitrarily large `|A|`). Same `Finset.filter`
vocabulary as the parent statement.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingCoprimeSparse

/-- For every nonempty pairwise coprime `A ⊆ ℕ_{>0}` with `2 (|A| - 1) < a` for all `a ∈ A`,
every `n ≥ max A` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ a ∈ A, a ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ a ∈ A, a ∣ k}`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) →
    (∀ a ∈ A, 2 * (A.card - 1) < a) →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingCoprimeSparse

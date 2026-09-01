import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# ErdosMultiplesDoublingGcdTail — Erdős #488 under a gcd-weighted tail condition

The instance of `Statements.ErdosMultiplesDoubling.statement` for every finite set `A` of
positive integers such that, for every `a ∈ A`,

  `∑_{b ∈ A, b > a} gcd(a, b) / b < 1/2`.

No primitivity or coprimality is assumed. For pairwise coprime `A` (in particular for any set of
primes) the condition reads `∑_{b ∈ A, b > a} 1/b < 1/2` for every `a ∈ A`, i.e. the reciprocal
sum of the elements above the least one is below `1/2` (the sums for larger `a` are then smaller).
Infinitely many sets of every cardinality satisfy it, e.g. `{3, 7, 11, 13}` or any eight primes
`≥ 17`.

Same `Finset.filter` vocabulary as the parent statement. Submissions **must not** import this
module.
-/

namespace Statements.ErdosMultiplesDoublingGcdTail

/-- For every finite `A ⊆ ℕ_{>0}`, nonempty, with `∑_{b ∈ A, a < b} gcd(a,b)/b < 1/2` for each
`a ∈ A`, every `n ≥ max A` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ a ∈ A, a ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ a ∈ A, a ∣ k}`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∀ a ∈ A, (∑ b ∈ A.filter (fun b => a < b), (Nat.gcd a b : ℚ) / b) < 1 / 2) →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingGcdTail

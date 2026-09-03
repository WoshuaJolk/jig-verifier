import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingMinTwo — Erdős #488 for every set containing the generator 2

The instance of `Statements.ErdosMultiplesDoubling.statement` for every finite `A` with
`2 ∈ A` (and `0 ∉ A`), of arbitrary cardinality, no primitivity assumed. Same `Finset.filter`
vocabulary as the parent statement.

Prior art: https://www.erdosproblems.com/forum/thread/488#post-5163 (MalekZ, 21:13 on 31 Mar
2026) gives this two-case split (all-even reduces to the a=2 singleton bound; else use an odd
generator together with 2) informally, for primitive A. The primitivity hypothesis is not
needed: the same argument gives the statement below for arbitrary A containing 2.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingMinTwo

/-- For every finite `A ⊆ ℕ_{>0}` with `2 ∈ A`, every `n ≥ max A` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ a ∈ A, a ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ a ∈ A, a ∣ k}`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A → 2 ∈ A →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
      n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
        2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingMinTwo

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# ErdosMultiplesDoublingGcdTailOrdered — Erdős #488 under an ordered gcd-weighted tail condition

The instance of `Statements.ErdosMultiplesDoubling.statement` for every finite set `A` of
positive integers that admits an injective rank `r : ℕ → ℕ` on `A` such that, for every `a ∈ A`,

  `∑_{b ∈ A, r b < r a} gcd(a, b) / b < 1/2`.

Taking `r` decreasing on `A` recovers `ErdosMultiplesDoublingGcdTail` (sum over `b > a`); the
freedom to choose the peeling order strictly enlarges the covered family, e.g. `{22, 28, 42, 52, 77}`
satisfies the ordered condition but not the decreasing one. Whether such an `r` exists is decided
by the greedy rule "repeatedly remove any element whose sum over the remaining others is `< 1/2`".

Same `Finset.filter` vocabulary as the parent statement. Submissions **must not** import this
module.
-/

namespace Statements.ErdosMultiplesDoublingGcdTailOrdered

/-- For every finite nonempty `A ⊆ ℕ_{>0}` admitting an injective rank `r` on `A` with
`∑_{b ∈ A, r b < r a} gcd(a,b)/b < 1/2` for each `a ∈ A`, every `n ≥ max A` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ a ∈ A, a ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ a ∈ A, a ∣ k}`. -/
abbrev statement : Prop :=
  ∀ A : Finset ℕ, A.Nonempty → 0 ∉ A →
    (∃ r : ℕ → ℕ, Set.InjOn r ↑A ∧
      ∀ a ∈ A, (∑ b ∈ A.filter (fun b => r b < r a), (Nat.gcd a b : ℚ) / b) < 1 / 2) →
    ∀ n m : ℕ, (∀ a ∈ A, a ≤ n) → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ a ∈ A, a ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ a ∈ A, a ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingGcdTailOrdered

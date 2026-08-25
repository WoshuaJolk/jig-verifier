import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

open scoped Pointwise

namespace Statements.Erdos52DominantCore

/--
The weighted additive-profile and internal product bounds force a quantitatively
large normalized layer among the first `r` valuation levels whenever
`2H < rN`.
-/
abbrev statement : Prop :=
  ∀ (m r H : ℕ) (L : ℕ → Finset ℕ), 0 < r → r ≤ m →
    let N := ∑ i ∈ Finset.range m, (L i).card
    let W := ∑ i ∈ Finset.range m, i * (L i).card
    W ≤ H →
    (∀ i < m, (L i * L i).card ≤ H) →
    2 * H < r * N →
    ∃ i < r,
      N < 2 * r * (L i).card ∧
      (L i * L i).card ≤ H

theorem target : statement := sorry

end Statements.Erdos52DominantCore

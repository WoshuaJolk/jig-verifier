import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingThreeCriterion — the integer union-bound criterion for primitive triples

For a primitive triple `a < b < c` (no element divides another) and every `n ≥ c`,

  `n / a + n / b + n / c + 3 ≤ 2 * #{k ∈ [1,n] : a ∣ k ∨ b ∣ k ∨ c ∣ k}`

(natural-number division). Equivalently, writing `ω(k)` for the number of generators dividing
`k`, `∑_{k ≤ n, k ∈ B} (2 - ω(k)) ≥ 3`. This is the hypothesis of the union-bound reduction
(`Statements.ErdosMultiplesDoublingSparse`), and hence implies the doubling inequality of
Erdős #488 for every primitive `|A| = 3`. The constant `3` is attained at `n = c`.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingThreeCriterion

/-- For every primitive triple `0 < a < b < c` and every `n ≥ c`,
`n / a + n / b + n / c + 3 ≤ 2 * #{k ∈ [1,n] : ∃ x ∈ {a, b, c}, x ∣ k}`. -/
abbrev statement : Prop :=
  ∀ a b c : ℕ, 0 < a → a < b → b < c → ¬ a ∣ b → ¬ a ∣ c → ¬ b ∣ c → ∀ n : ℕ, c ≤ n →
    n / a + n / b + n / c + 3 ≤
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingThreeCriterion

import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingFour — the primitive four-generator case of Erdős #488

The instance `A = {a, b, c, d}` of `Statements.ErdosMultiplesDoubling.statement` for every
primitive quadruple `0 < a < b < c < d` (no element divides another), all `n ≥ d` and all
`m > n`. Same `Finset.filter` vocabulary as the parent statement. Together with the one-, two-
and three-generator statements this covers every `|A| ≤ 4` (a non-primitive set has the same
set of multiples as its primitive reduction, which is smaller).

Chojecki (https://www.ulam.ai/research/erdos488.pdf, Cor. 4.7) proves `|A| ≤ 3`; `|A| = 4` is the
first case beyond that frontier.

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingFour

/-- For every primitive quadruple `0 < a < b < c < d`, every `n ≥ d` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ x ∈ {a,b,c,d}, x ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ x ∈ {a,b,c,d}, x ∣ k}`. -/
abbrev statement : Prop :=
  ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    ¬ a ∣ b → ¬ a ∣ c → ¬ a ∣ d → ¬ b ∣ c → ¬ b ∣ d → ¬ c ∣ d →
    ∀ n m : ℕ, d ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingFour

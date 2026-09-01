import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingFourCriterion — the union-bound inequality for primitive 4-sets

For a primitive set `G = {a < b < c < d}` (no element divides another) and every `n ≥ d`,

  `⌊n/a⌋ + ⌊n/b⌋ + ⌊n/c⌋ + ⌊n/d⌋ + 4 ≤ 2 · #{k ∈ [1,n] : some g ∈ G divides k}`.

This is Chojecki's inequality (10) (https://www.ulam.ai/research/erdos488.pdf, Prop. 6.5) for
`|G| = 4`, with no sparsity or excess hypothesis.  Together with the union-bound criterion
(`ErdosMultiplesDoublingSparse`, which needs only `∑ ⌊n/g⌋ < 2 M(n)`) it gives Erdős #488 for
every set whose primitive reduction has four elements — the first case beyond Chojecki's `|G| ≤ 3`.
(Statement 8 shows (10) fails for some primitive `|G| = 10`.)

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingFourCriterion

abbrev statement : Prop :=
  ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
    ¬ a ∣ b → ¬ a ∣ c → ¬ a ∣ d → ¬ b ∣ c → ¬ b ∣ d → ¬ c ∣ d →
    ∀ n : ℕ, d ≤ n →
    n / a + n / b + n / c + n / d + 4 ≤
      2 * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c, d} : Finset ℕ), x ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingFourCriterion

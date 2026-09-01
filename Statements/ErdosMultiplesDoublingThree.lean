import Mathlib.Order.Interval.Finset.Nat

/-!
# ErdosMultiplesDoublingThree — the primitive three-generator case of Erdős #488

The instance `A = {a, b, c}` of `Statements.ErdosMultiplesDoubling.statement` for every
primitive triple `0 < a < b < c` (no element divides another), all `n ≥ c` and all `m > n`.
Same `Finset.filter` vocabulary as the parent statement. Together with the one- and
two-generator statements this covers every `|A| = 3` (a non-primitive triple has the same set
of multiples as its primitive reduction, of size `≤ 2`).

Submissions **must not** import this module.
-/

namespace Statements.ErdosMultiplesDoublingThree

/-- For every primitive triple `0 < a < b < c`, every `n ≥ c` and every `m > n`,
`n * #{k ∈ [1,m] : ∃ x ∈ {a,b,c}, x ∣ k} < 2 * m * #{k ∈ [1,n] : ∃ x ∈ {a,b,c}, x ∣ k}`. -/
abbrev statement : Prop :=
  ∀ a b c : ℕ, 0 < a → a < b → b < c → ¬ a ∣ b → ¬ a ∣ c → ¬ b ∣ c →
    ∀ n m : ℕ, c ≤ n → n < m →
    n * ((Finset.Icc 1 m).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card <
      2 * m * ((Finset.Icc 1 n).filter (fun k => ∃ x ∈ ({a, b, c} : Finset ℕ), x ∣ k)).card

theorem target : statement := sorry

end Statements.ErdosMultiplesDoublingThree

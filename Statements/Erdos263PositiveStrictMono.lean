import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace Statements.Erdos263PositiveStrictMono

/-- The sequence in corrected Erdős 263 satisfies its positivity and strict
monotonicity requirements. -/
abbrev statement : Prop :=
  (∀ n : ℕ, 0 < 2 ^ 2 ^ n) ∧ StrictMono (fun n : ℕ => 2 ^ 2 ^ n)

theorem target : statement := sorry

end Statements.Erdos263PositiveStrictMono

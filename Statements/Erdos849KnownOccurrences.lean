import Mathlib.Data.Nat.Choose.Basic

namespace Statements.Erdos849KnownOccurrences

/-- Three distinct lower-half occurrences of `120` in Pascal's triangle. -/
abbrev statement : Prop :=
  1 ≤ 3 ∧ 2 * 3 ≤ 10 ∧ Nat.choose 10 3 = 120 ∧
  1 ≤ 2 ∧ 2 * 2 ≤ 16 ∧ Nat.choose 16 2 = 120 ∧
  1 ≤ 1 ∧ 2 * 1 ≤ 120 ∧ Nat.choose 120 1 = 120

theorem target : statement := sorry

end Statements.Erdos849KnownOccurrences

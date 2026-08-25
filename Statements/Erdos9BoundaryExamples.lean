import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Statements.Erdos9BoundaryExamples

def Exceptional : Set ℕ :=
  {n | Odd n ∧ ¬ ∃ (p k l : ℕ), Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l}

/-- The first two exceptional odd integers and the first represented
odd integer, checking both directions of the defining predicate. -/
abbrev statement : Prop :=
  1 ∈ Exceptional ∧ 3 ∈ Exceptional ∧ 5 ∉ Exceptional

theorem target : statement := sorry

end Statements.Erdos9BoundaryExamples

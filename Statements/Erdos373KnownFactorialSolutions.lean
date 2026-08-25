import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorial.Basic

namespace Statements.Erdos373KnownFactorialSolutions

open scoped Nat

abbrev IsSolution (candidate : ℕ × List ℕ) : Prop :=
  candidate.1 ! = (candidate.2.map Nat.factorial).prod ∧
  candidate.2.Pairwise (· ≥ ·) ∧
  candidate.2.headI < candidate.1 - 1 ∧
  ∀ a ∈ candidate.2, 1 < a

/-- Two published nontrivial solutions, including Hickerson's conjectured
largest one. -/
abbrev statement : Prop :=
  IsSolution (10, [7, 6]) ∧ IsSolution (16, [14, 5, 2])

theorem target : statement := sorry

end Statements.Erdos373KnownFactorialSolutions

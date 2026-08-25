import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card

namespace Statements.Erdos417ValueOneBoundary

open Set

/-- The value one occurs in both counting sets at threshold one. -/
abbrev statement : Prop :=
  (1 : ℕ) ∈ {k : ℕ | k ∈ Set.range Nat.totient ∧ k ≤ 1} ∧
  (1 : ℕ) ∈ Nat.totient '' Set.Icc 1 1

theorem target : statement := sorry

end Statements.Erdos417ValueOneBoundary

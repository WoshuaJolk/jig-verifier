import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Statements.Erdos10LinearPowerBound

abbrev represented (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exponents : Multiset ℕ),
    p.Prime ∧ exponents.card ≤ k ∧
      n = p + (exponents.map (fun e => (2 : ℕ) ^ e)).sum

/-- A nonuniform baseline: every `n ≥ 2` is a prime plus at most `n` powers of two. The open Erdős problem asks for one uniform bound. -/
abbrev statement : Prop :=
  ∀ n ≥ 2, represented n n

theorem target : statement := sorry

end Statements.Erdos10LinearPowerBound

import Mathlib.Data.Nat.Factorization.Basic

namespace Statements.Erdos930ValuationOneObstruction

/-- A natural number with some prime occurring to exponent exactly one cannot
be a perfect power of exponent greater than one. -/
abbrev statement : Prop :=
  ∀ N p : ℕ, p.Prime → N.factorization p = 1 →
    ¬ ∃ m l : ℕ, 1 < l ∧ m ^ l = N

theorem target : statement := sorry

end Statements.Erdos930ValuationOneObstruction

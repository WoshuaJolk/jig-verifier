import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Statements.Erdos699CaseIOne

/-- The case `i = 1` of Erdős Problem 699: for `1 < j ≤ n / 2`, some prime divides
`gcd (C(n,1), C(n,j))`. This is the observation `gcd (C(n,i), C(n,j)) > 1` of Erdős and
Szekeres at `i = 1`; the bound `p ≥ 1` is automatic. -/
abbrev statement : Prop :=
  ∀ n j : ℕ, 1 < j → j ≤ n / 2 →
    ∃ p : ℕ, p.Prime ∧ 1 ≤ p ∧ p ∣ Nat.gcd (n.choose 1) (n.choose j)

theorem target : statement := sorry

end Statements.Erdos699CaseIOne

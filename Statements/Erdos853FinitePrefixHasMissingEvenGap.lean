import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos853FinitePrefixHasMissingEvenGap

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- Every finite prefix of the consecutive-prime gaps omits a positive even
integer, so the set defining `r(x)` in Erdős Problem 853 is nonempty. -/
abbrev statement : Prop :=
  ∀ x : ℕ, ∃ t : ℕ, 0 < t ∧ t % 2 = 0 ∧
    ¬∃ n ≤ x, primeGap n = t

theorem target : statement := sorry

end Statements.Erdos853FinitePrefixHasMissingEvenGap

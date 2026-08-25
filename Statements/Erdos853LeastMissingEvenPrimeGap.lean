import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos853LeastMissingEvenPrimeGap

open Filter

noncomputable def primeGap (n : ℕ) : ℕ :=
  (n + 1).nth Nat.Prime - n.nth Nat.Prime

noncomputable def r (x : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ t % 2 = 0 ∧ ¬∃ n ≤ x, primeGap n = t}

/-- Erdős Problem 853(i): the least positive even gap absent among the first
`x+1` consecutive-prime gaps tends to infinity. -/
abbrev statement : Prop :=
  Tendsto r atTop atTop

theorem target : statement := sorry

end Statements.Erdos853LeastMissingEvenPrimeGap

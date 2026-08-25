import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos390FactorialFactorLimit

open Filter Asymptotics Real
open scoped Nat

/-- The least possible largest factor in a factorization of `n!` into
distinct integers greater than `n`. -/
noncomputable def extremalFactor (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k, ∃ a : ℕ → ℕ, StrictMono a ∧
    n < a 0 ∧ a (k - 1) = m ∧ ∏ i < k, a i = n !}

/-- Erdős problem 390: the known order of magnitude for the excess over
`2n` has a true asymptotic constant. -/
abbrev statement : Prop :=
  ∃ c : ℝ,
    (fun n : ℕ => (extremalFactor n : ℝ) - 2 * n) ~[atTop]
      (fun n : ℕ => c * n / log (n : ℝ))

theorem target : statement := sorry

end Statements.Erdos390FactorialFactorLimit

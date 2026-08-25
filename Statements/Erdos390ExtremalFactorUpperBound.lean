import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace Statements.Erdos390ExtremalFactorUpperBound

open scoped Nat

noncomputable def extremalFactor (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k, ∃ a : ℕ → ℕ, StrictMono a ∧
    n < a 0 ∧ a (k - 1) = m ∧ ∏ i < k, a i = n !}

/-- For every `n ≥ 3`, the defining set for the extremal factor is
nonempty and the one-factor decomposition gives the elementary upper
bound `f(n) ≤ n!`. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 3 ≤ n → extremalFactor n ≤ n !

theorem target : statement := sorry

end Statements.Erdos390ExtremalFactorUpperBound

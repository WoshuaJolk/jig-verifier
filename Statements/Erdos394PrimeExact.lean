import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Lattice.Nat

open Nat Finset

namespace Statements.Erdos394PrimeExact

noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i)}

/-- For a prime `p`, the first pair of consecutive positive integers whose product is divisible by `p` starts at `p - 1`. -/
abbrev statement : Prop :=
  ∀ p : ℕ, p.Prime → t 2 p = p - 1

theorem target : statement := sorry

end Statements.Erdos394PrimeExact

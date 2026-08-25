import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos373FactorialProductFiniteness

open scoped Nat

abbrev solutions : Set (ℕ × List ℕ) :=
  {(n, factors) |
    n ! = (factors.map Nat.factorial).prod ∧
    factors.Pairwise (· ≥ ·) ∧
    factors.headI < n - 1 ∧
    ∀ a ∈ factors, 1 < a}

/-- Erdős Problem 373: only finitely many nontrivial factorial-product
solutions exist. -/
abbrev statement : Prop :=
  solutions.Finite

theorem target : statement := sorry

end Statements.Erdos373FactorialProductFiniteness

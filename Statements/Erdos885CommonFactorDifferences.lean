import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card

open Set

namespace Statements.Erdos885CommonFactorDifferences

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Nat.dist a b}

/-- Erdős Problem 885: for every positive `k`, some `k` positive integers
have at least `k` common factor differences. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ Ns : Finset ℕ,
    Ns.card = k ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

theorem target : statement := sorry

end Statements.Erdos885CommonFactorDifferences

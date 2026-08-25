import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card

open Set

namespace Statements.Erdos885TwoIntegerBoundary

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Nat.dist a b}

/-- The source's first solved case: two positive distinct integers have at
least two common factor differences. -/
abbrev statement : Prop :=
  ∃ Ns : Finset ℕ,
    Ns.card = 2 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2

theorem target : statement := sorry

end Statements.Erdos885TwoIntegerBoundary

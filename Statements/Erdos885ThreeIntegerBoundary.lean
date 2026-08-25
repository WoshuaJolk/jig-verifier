import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card

open Set

namespace Statements.Erdos885ThreeIntegerBoundary

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Nat.dist a b}

/-- The `k = 3` case of Erdős 885. -/
abbrev statement : Prop :=
  ∃ Ns : Finset ℕ,
    Ns.card = 3 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3

theorem target : statement := sorry

end Statements.Erdos885ThreeIntegerBoundary

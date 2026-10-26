import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Card

open Set

namespace Statements.Erdos885FourIntegerBoundary

def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ d = Nat.dist a b}

/-- The known k = 4 case of Erdős Problem 885. -/
abbrev statement : Prop :=
  ∃ Ns : Finset ℕ,
    Ns.card = 4 ∧ (∀ n ∈ Ns, 1 ≤ n) ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4

theorem target : statement := sorry

end Statements.Erdos885FourIntegerBoundary

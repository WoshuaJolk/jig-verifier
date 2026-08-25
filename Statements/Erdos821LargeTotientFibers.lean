import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card

namespace Statements.Erdos821LargeTotientFibers

/-- The number of natural numbers with Euler totient equal to `n`. -/
noncomputable def totientFiberCount (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

/-- Erdős Problem 821: totient fibers attain exponent arbitrarily close to one
infinitely often. -/
abbrev statement : Prop :=
  ∀ ε > (0 : ℝ),
    Set.Infinite
      {n : ℕ |
        (totientFiberCount n : ℝ) > (n : ℝ) ^ (1 - ε)}

theorem target : statement := sorry

end Statements.Erdos821LargeTotientFibers

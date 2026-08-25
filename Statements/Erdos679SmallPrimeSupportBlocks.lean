import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos679SmallPrimeSupportBlocks

def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

/-- The surviving first question of Erdős Problem 679. The threshold K is
chosen from ε before the infinite set of endpoints n. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, Set.Infinite
      {n : ℕ | ∀ k : ℕ, K ≤ k → k < n →
        (omega (n - k) : ℝ) <
          (1 + ε) * Real.log k / Real.log (Real.log k)}

theorem target : statement := sorry

end Statements.Erdos679SmallPrimeSupportBlocks

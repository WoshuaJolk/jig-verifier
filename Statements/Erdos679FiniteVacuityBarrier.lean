import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic

namespace Statements.Erdos679FiniteVacuityBarrier

def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

def GoodEndpoint (ε : ℝ) (K n : ℕ) : Prop :=
  ∀ k : ℕ, K ≤ k → k < n →
    (omega (n - k) : ℝ) <
      (1 + ε) * Real.log k / Real.log (Real.log k)

/-- The small endpoints satisfying the inner condition vacuously never supply
the infinitude required by Erdős Problem 679. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, ∀ K : ℕ,
    (∀ n : ℕ, n ≤ K → GoodEndpoint ε K n) ∧
      Set.Finite {n : ℕ | n ≤ K}

theorem target : statement := sorry

end Statements.Erdos679FiniteVacuityBarrier

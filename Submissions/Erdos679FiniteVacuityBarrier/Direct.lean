import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Submissions.Erdos679FiniteVacuityBarrier.Direct

def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

def GoodEndpoint (ε : ℝ) (K n : ℕ) : Prop :=
  ∀ k : ℕ, K ≤ k → k < n →
    (omega (n - k) : ℝ) <
      (1 + ε) * Real.log k / Real.log (Real.log k)

theorem proof :
    ∀ ε : ℝ, ∀ K : ℕ,
      (∀ n : ℕ, n ≤ K → GoodEndpoint ε K n) ∧
        Set.Finite {n : ℕ | n ≤ K} := by
  intro ε K
  constructor
  · intro n hn k hk hkn
    omega
  · exact Set.finite_Iic K

end Submissions.Erdos679FiniteVacuityBarrier.Direct

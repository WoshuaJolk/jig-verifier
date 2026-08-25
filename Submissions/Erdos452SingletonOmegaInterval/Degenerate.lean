import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Submissions.Erdos452SingletonOmegaInterval.Degenerate

def omega (n : ℕ) : ℕ := n.primeFactorsList.length

def HasOmegaRichInterval (x k : ℕ) : Prop :=
  ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x + 1 ∧
    (Real.log (x : ℝ)) ^ k ≤ L ∧
      ∀ n : ℕ, a ≤ n → n < a + L →
        Real.log (Real.log (n : ℝ)) < omega n

/-- Must-fail control: adds an impossible hypothesis. -/
theorem proof : False → HasOmegaRichInterval 3 0 := False.elim

end Submissions.Erdos452SingletonOmegaInterval.Degenerate

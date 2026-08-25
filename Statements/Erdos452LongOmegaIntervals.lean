import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Statements.Erdos452LongOmegaIntervals

def omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- A consecutive interval in `[x,2x]` of length at least `(log x)^k`
    on which every integer has more than `log log n` distinct prime factors. -/
def HasOmegaRichInterval (x k : ℕ) : Prop :=
  ∃ a L : ℕ, x ≤ a ∧ a + L ≤ 2 * x + 1 ∧
    (Real.log (x : ℝ)) ^ k ≤ L ∧
      ∀ n : ℕ, a ≤ n → n < a + L →
        Real.log (Real.log (n : ℝ)) < omega n

/-- The unbounded-exponent conjectural part of Erdős problem 452. -/
abbrev statement : Prop :=
  ∀ K : ℕ, ∃ k x : ℕ, K ≤ k ∧ 3 ≤ x ∧ HasOmegaRichInterval x k

theorem target : statement := sorry

end Statements.Erdos452LongOmegaIntervals

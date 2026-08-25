import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

namespace Statements.Erdos126AdditivePrimeFactors

open Filter
open scoped Topology

/-- `f n` is the largest universal lower bound for the number of distinct
prime factors in the product of all ordered pairwise sums from an `n`-set. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n,
    IsGreatest
      {m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ p ∈ A.offDiag, (p.1 + p.2)).primeFactors.card}
      (f n)

/-- Erdős problem 126: the universal number of distinct prime factors grows
faster than every constant multiple of `log n`. -/
abbrev statement : Prop :=
  ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log n) atTop atTop

theorem target : statement := sorry

end Statements.Erdos126AdditivePrimeFactors

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos726HalfPrimeReciprocalMass

open Nat Filter Finset
open scoped Topology Asymptotics

/-- Erdős problem 726: primes `p ≤ n` for which the least residue of `n`
lies in the upper half modulo `p` carry asymptotically half the total
reciprocal-prime mass. -/
abbrev statement : Prop :=
  (fun n : ℕ =>
      ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ => p.Prime ∧ (p : ℝ) / 2 < (n % p : ℝ)),
        (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ => Real.log (Real.log (n : ℝ)) / 2)

theorem target : statement := sorry

end Statements.Erdos726HalfPrimeReciprocalMass

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos882DivisibilityAntichainSubsetSums

open Finset

def nonemptySubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image fun B => B.sum id

def DivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

/-- The likely sharp upper-bound conjecture in Erdős problem 882. -/
abbrev statement : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 n →
    DivisibilityAntichain (nonemptySubsetSums A) →
    (A.card : ℝ) ≤ Real.log n / Real.log 2 + C

theorem target : statement := sorry

end Statements.Erdos882DivisibilityAntichainSubsetSums

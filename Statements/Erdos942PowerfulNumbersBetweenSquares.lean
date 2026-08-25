import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Statements.Erdos942PowerfulNumbersBetweenSquares

open Nat Filter Topology

def Full (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful (n : ℕ) : Prop := Full 2 n

instance powerfulDecidable : ∀ n, Decidable (Powerful n) := by
  intro n
  dsimp [Powerful, Full]
  infer_instance

def count (n : ℕ) : ℕ :=
  ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

/-- Erdős problem 942: the maximal order of the number of powerful integers
between consecutive squares is a fixed power of the logarithm. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ o : ℕ → ℝ,
    o =o[atTop] (1 : ℕ → ℝ) ∧
    (∀ᶠ n in atTop, count n < (Real.log n) ^ (c + o n)) ∧
    {n | count n > (Real.log n) ^ (c - o n)}.Infinite

theorem target : statement := sorry

end Statements.Erdos942PowerfulNumbersBetweenSquares

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Topology

/-!
# Erdős problem 852, remaining open upper-bound question

Is the longest run of pairwise distinct consecutive prime gaps among starting
indices below `x` of length `o(log x)`?
-/

namespace Statements.Erdos852DistinctPrimeGaps

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

def DistinctRun (start length : ℕ) : Prop :=
  (Finset.range length : Set ℕ).Pairwise fun i j =>
    primeGap (start + i) ≠ primeGap (start + j)

noncomputable def longestRun (x : ℕ) : ℕ :=
  sSup {length : ℕ | ∃ start < x, DistinctRun start length}

abbrev statement : Prop :=
  Tendsto
    (fun x : ℕ => (longestRun x : ℝ) / Real.log x)
    atTop (𝓝 0)

theorem target : statement := sorry

end Statements.Erdos852DistinctPrimeGaps

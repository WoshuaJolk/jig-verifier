import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open Filter Finset
open scoped Asymptotics Topology

namespace Statements.Erdos400FactorialPackingMean

noncomputable def g (k n : ℕ) : ℕ :=
  sSup {x | ∃ a : Fin k → ℕ,
    (∏ i, Nat.factorial (a i)) ∣ Nat.factorial n ∧ x = (∑ i, a i) - n}

/-- Part (i) of Erdős Problem 400. -/
abbrev statement : Prop :=
  ∀ k : ℕ, k ≥ 2 → ∃ c : ℝ,
    (fun x : ℕ ↦ ∑ n ∈ Icc 1 x, (g k n : ℝ)) ~[atTop]
      (fun x : ℕ ↦ c * x * Real.log x)

theorem target : statement := sorry

end Statements.Erdos400FactorialPackingMean

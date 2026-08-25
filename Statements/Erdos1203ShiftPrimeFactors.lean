import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter
open scoped Topology

/-!
# Erdős problem 1203

For `F(n) = sup_k ω(n+k) log(log k) / log k`, prove `F(n) → ∞`.
-/

namespace Statements.Erdos1203ShiftPrimeFactors

noncomputable def F (n : ℕ) : ℝ :=
  ⨆ k : ℕ,
    (Nat.primeFactors (n + k)).card *
      (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))

abbrev statement : Prop := Tendsto F atTop atTop

theorem target : statement := sorry

end Statements.Erdos1203ShiftPrimeFactors

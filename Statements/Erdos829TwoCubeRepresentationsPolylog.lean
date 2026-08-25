import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos829TwoCubeRepresentationsPolylog

open Filter

def isCube (m : ℕ) : Bool :=
  (List.range (m + 1)).any fun k ↦ k ^ 3 == m

def sumRepCubes (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a ↦ isCube a && isCube (n - a)).card

/-- Erdős Problem 829: the ordered representation count of an integer as a
sum of two nonnegative cubes has some fixed polylogarithmic upper bound. -/
abbrev statement : Prop :=
  ∃ C : ℕ, (fun n : ℕ ↦ (sumRepCubes n : ℝ)) =O[atTop]
    fun n : ℕ ↦ (Real.log n) ^ C

theorem target : statement := sorry

end Statements.Erdos829TwoCubeRepresentationsPolylog

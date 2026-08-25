import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Statements.Erdos236PrimePowerRepresentationsSublog

open Filter Asymptotics

def representationCount (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter
    (fun k => Nat.Prime (n - 2 ^ k))).length

/-- Erdős problem 236. -/
abbrev statement : Prop :=
  (fun n => (representationCount n : ℝ)) =o[atTop]
    (fun n => Real.log (n : ℝ))

theorem target : statement := sorry

end Statements.Erdos236PrimePowerRepresentationsSublog

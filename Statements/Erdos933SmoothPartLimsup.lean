import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Order.LiminfLimsup

open Filter

namespace Statements.Erdos933SmoothPartLimsup

def twoValuation (n : ℕ) : ℕ := padicValNat 2 (n * (n + 1))

def threeValuation (n : ℕ) : ℕ := padicValNat 3 (n * (n + 1))

/-- Erdős Problem 933: the 2,3-smooth part of n(n+1), normalized by
n log n, has infinite limsup. -/
abbrev statement : Prop :=
  atTop.limsup (fun n : ℕ ↦
    ((((2 ^ twoValuation n * 3 ^ threeValuation n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (n : ℝ))) : EReal)) = ⊤

theorem target : statement := sorry

end Statements.Erdos933SmoothPartLimsup

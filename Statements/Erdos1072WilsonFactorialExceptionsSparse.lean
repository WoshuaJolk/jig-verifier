import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Lattice.Nat

open Asymptotics Filter Set

namespace Statements.Erdos1072WilsonFactorialExceptionsSparse

noncomputable def firstFactorialNegOne (p : ℕ) : ℕ :=
  sInf {n : ℕ | n.factorial + 1 ≡ 0 [MOD p]}

/-- The explicit Hardy--Subbarao sparsity variant of Erdős Problem 1072. -/
abbrev statement : Prop :=
  (fun x : ℕ =>
      (({p : ℕ | p.Prime ∧ firstFactorialNegOne p = p - 1} ∩ Icc 0 x).ncard : ℝ))
    =o[atTop] (fun x : ℕ => (x : ℝ) / Real.log x)

theorem target : statement := sorry

end Statements.Erdos1072WilsonFactorialExceptionsSparse

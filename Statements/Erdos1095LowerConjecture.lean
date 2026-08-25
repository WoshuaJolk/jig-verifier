import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Topology.Instances.Nat

open Nat Real Filter
open scoped Topology

namespace Statements.Erdos1095LowerConjecture

/-- The Erdős–Selfridge function: the least `n>k+1` for which every
prime factor of `choose n k` exceeds `k`. -/
noncomputable def g (k : ℕ) : ℕ :=
  sInf {n : ℕ | k + 1 < n ∧ k < (n.choose k).minFac}

/-- The conjectural exponential lower bound for the Erdős–Selfridge
function. -/
abbrev statement : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
    exp (c * k / Real.log k) ≤ g k

theorem target : statement := sorry

end Statements.Erdos1095LowerConjecture

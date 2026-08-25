import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Statements.Erdos394HallLogSaving

/-- The least positive `m` such that `n` divides a product of `k` consecutive natural numbers beginning at `m`. -/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i)}

/-- The sharp Erdős–Hall conjecture in Problem 394: every logarithmic saving exponent below `log 2` gives a little-o upper bound. -/
abbrev statement : Prop :=
  ∀ c < Real.log 2,
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ 2 / (Real.log x) ^ c)

theorem target : statement := sorry

end Statements.Erdos394HallLogSaving

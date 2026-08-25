import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Statements.Erdos66LogRepresentationLimit

open Filter
open scoped Topology

/-- The ordered additive representation function `1_A * 1_A(n)`, inlined
from the formal-conjectures vocabulary. -/
noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A).card

/-- Erdős problem 66: some additive representation function has a finite,
nonzero logarithmic asymptotic. -/
abbrev statement : Prop :=
  ∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)

theorem target : statement := sorry

end Statements.Erdos66LogRepresentationLimit

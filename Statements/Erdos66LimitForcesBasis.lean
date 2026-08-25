import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Statements.Erdos66LimitForcesBasis

open Filter
open scoped Topology

noncomputable def sumRep (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.antidiagonal n).filter
    fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A).card

/-- Any nonzero logarithmic limit would force `A` to be an asymptotic
additive basis of order two. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (c : ℝ), c ≠ 0 →
    Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) →
    ∀ᶠ n : ℕ in atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n

theorem target : statement := sorry

end Statements.Erdos66LimitForcesBasis

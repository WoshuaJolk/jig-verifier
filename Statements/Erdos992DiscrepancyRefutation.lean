import Mathlib

namespace Statements.Erdos992DiscrepancyRefutation

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators

/-- The number of the first `N` fractional parts lying in `[a,b)`. -/
noncomputable def intervalCount (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ Ico a b).card

/-- Half-open subintervals of `[0,1]`, represented by endpoints. -/
def UnitSubinterval := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

/-- The signed discrepancy error associated with one interval. -/
noncomputable def intervalError (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    (I : UnitSubinterval) : ℝ :=
  intervalCount x α N I.1.1 I.1.2 - (I.1.2 - I.1.1) * N

/-- The unnormalised interval discrepancy from Erdős Problem 992. -/
noncomputable def intervalDiscrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : UnitSubinterval ↦ |intervalError x α N I|)

/-- Berkes--Philipp's negative resolution of Erdős Problem 992: one strictly
increasing integer sequence has discrepancy at least a fixed positive multiple
of `sqrt (N log N)` infinitely often for almost every `α ∈ [0,1]`. -/
abbrev statement : Prop :=
  ∃ x : ℕ → ℤ, StrictMono x ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ᵐ α : ℝ ∂volume, α ∈ Icc 0 1 →
        ∃ᶠ N : ℕ in atTop,
          c * Real.sqrt ((N : ℝ) * Real.log N) ≤
            intervalDiscrepancy x α N

theorem target : statement := by
  sorry

end Statements.Erdos992DiscrepancyRefutation

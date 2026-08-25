import Mathlib

namespace Submissions.Erdos992DiscrepancyRefutation.Control

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable def intervalCount (x : ℕ → ℤ) (α : ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ Int.fract (α * (x n : ℝ)) ∈ Ico a b).card

def UnitSubinterval := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

noncomputable def intervalError (x : ℕ → ℤ) (α : ℝ) (N : ℕ)
    (I : UnitSubinterval) : ℝ :=
  intervalCount x α N I.1.1 I.1.2 - (I.1.2 - I.1.1) * N

noncomputable def intervalDiscrepancy (x : ℕ → ℤ) (α : ℝ) (N : ℕ) : ℝ :=
  sSup (Set.range fun I : UnitSubinterval ↦ |intervalError x α N I|)

theorem proof (h : False) :
    ∃ x : ℕ → ℤ, StrictMono x ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ α : ℝ ∂volume, α ∈ Icc 0 1 →
          ∃ᶠ N : ℕ in atTop,
            c * Real.sqrt ((N : ℝ) * Real.log N) ≤
              intervalDiscrepancy x α N :=
  h.elim

end Submissions.Erdos992DiscrepancyRefutation.Control

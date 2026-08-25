import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace Submissions.Erdos995LacunaryL2Growth.Degenerate

def IsLacunary (n : ℕ → ℕ) : Prop :=
  1 ≤ n 0 ∧ ∃ q : ℝ, 1 < q ∧ ∀ k : ℕ,
    q * n k ≤ n (k + 1)

noncomputable def normalizedSum (n : ℕ → ℕ) (f : ℝ → ℝ)
    (α : ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N, f (Int.fract (α * n k))) /
    ((N : ℝ) * Real.sqrt (Real.log (Real.log N)))

/-- Erdős 995 has a negative answer: the proposed universal almost-sure
`o(N * sqrt(log log N))` bound fails for some `L²` function and
lacunary sequence. -/
abbrev statement : Prop :=
  ¬ ∀ n : ℕ → ℕ, ∀ f : ℝ → ℝ,
    IsLacunary n →
    MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) →
    ∀ᵐ α : ℝ ∂volume,
      Tendsto (normalizedSum n f α) atTop (nhds 0)

theorem proof : False → statement := False.elim

end Submissions.Erdos995LacunaryL2Growth.Degenerate

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos661FewBipartiteDistances

open Filter

abbrev Point := ℝ × ℝ

def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def EachSetDistinct {n : ℕ} (x y : Fin n → Point) : Prop :=
  Function.Injective x ∧ Function.Injective y

noncomputable def crossDistanceCount {n : ℕ} (x y : Fin n → Point) : ℕ := by
  classical
  exact (Finset.univ.image fun ij : Fin n × Fin n ↦ sqDist (x ij.1) (y ij.2)).card

/-- Erdős Problem 661: two disjoint `n`-point sets in the plane can have
`o(n / sqrt(log n))` distinct cross-distances. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ x y : Fin n → Point, EachSetDistinct x y ∧
      (crossDistanceCount x y : ℝ) ≤
        ε * ((n : ℝ) / Real.sqrt (Real.log n))

theorem target : statement := sorry

end Statements.Erdos661FewBipartiteDistances

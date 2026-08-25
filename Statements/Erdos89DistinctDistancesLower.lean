import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.Nat

namespace Statements.Erdos89DistinctDistancesLower

open Filter

abbrev Point := EuclideanSpace ℝ (Fin 2)

def distanceSet {n : ℕ} (points : Fin n → Point) : Set ℝ :=
  {d : ℝ | ∃ i j : Fin n, i ≠ j ∧ dist (points i) (points j) = d}

noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Fin n → Point,
    Function.Injective points ∧ (distanceSet points).ncard = m}

/-- Erdős Problem 89: every n-point planar configuration determines at least
a constant multiple of n / sqrt(log n) distinct distances. -/
abbrev statement : Prop :=
  (fun (n : ℕ) => (n : ℝ) / Real.sqrt (Real.log n)) =O[atTop]
    (fun n => (minimalDistinctDistances n : ℝ))

theorem target : statement := sorry

end Statements.Erdos89DistinctDistancesLower

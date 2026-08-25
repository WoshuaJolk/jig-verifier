import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card

namespace Statements.Erdos604SingletonPinnedDistance

/-- A singleton point set determines exactly one pinned distance, namely zero. -/
abbrev statement : Prop :=
  ((({0} : Finset (EuclideanSpace ℝ (Fin 2))).image
    fun y => dist 0 y).card) = 1

theorem target : statement := sorry

end Statements.Erdos604SingletonPinnedDistance

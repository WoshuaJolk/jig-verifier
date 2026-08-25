import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

open Asymptotics Filter

namespace Statements.Erdos653LocalDistanceDiversity

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Number of distinct distances from `p` to points of `X`, including zero when `p ∈ X`. This uniform `+1` does not change equality of local counts. -/
noncomputable def distinctDistancesFrom (X : Finset Point) (p : Point) : ℕ :=
  (X.image fun x => dist x p).card

/-- Maximum number of distinct local-distance counts among an `n`-point set. -/
noncomputable def maximalDistinctDistancesFrom (n : ℕ) : ℕ :=
  sSup {(X.image (distinctDistancesFrom X)).card |
    (X : Finset Point) (_ : X.card = n)}

/-- Erdős problem 653: asymptotically almost every point can have a different number of distances to the other points. -/
abbrev statement : Prop :=
  ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (1 - o n) * n ≤ maximalDistinctDistancesFrom n

theorem target : statement := sorry

end Statements.Erdos653LocalDistanceDiversity

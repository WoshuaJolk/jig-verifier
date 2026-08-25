import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős problem 1083

For fixed `d ≥ 3`, must every `n`-point subset of `ℝ^d` determine
`n^(2/d-o(1))` distinct distances?
-/

namespace Statements.Erdos1083DistinctDistances

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def distanceCount {d : ℕ} (P : Finset (Space d)) : ℕ :=
  (((P ×ˢ P).filter fun q => q.1 ≠ q.2).image fun q => dist q.1 q.2).card

abbrev statement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        ∀ P : Finset (Space d), P.card = n →
          (n : ℝ) ^ ((2 : ℝ) / d - ε) ≤ distanceCount P

theorem target : statement := sorry

end Statements.Erdos1083DistinctDistances

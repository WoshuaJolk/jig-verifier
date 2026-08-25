import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Order.OrderClosed

open Filter Metric
open scoped Topology

/-!
# Erdős problem 132

Every sufficiently large planar point set should determine arbitrarily many
distances which occur, but occur on at most `n` unordered pairs.

The implementation counts ordered pairs, so the faithful threshold is `2 * n`.
-/

namespace Statements.Erdos132SparseDistances

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def distanceMultiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  (A.offDiag.filter fun p => dist p.1 p.2 = d).card

noncomputable def goodDistances (A : Finset Point) : Finset ℝ :=
  (A.offDiag.image fun p => dist p.1 p.2).filter fun d =>
    0 < distanceMultiplicity A d ∧ distanceMultiplicity A d ≤ 2 * A.card

noncomputable def goodDistanceCount (A : Finset Point) : ℕ :=
  (goodDistances A).card

abbrev statement : Prop :=
  (∀ A : Finset Point, 5 ≤ A.card → 2 ≤ goodDistanceCount A) ∧
    ∀ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset Point, A.card = n → K ≤ goodDistanceCount A

theorem target : statement := sorry

end Statements.Erdos132SparseDistances

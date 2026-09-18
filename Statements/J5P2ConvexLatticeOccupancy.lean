import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Card

namespace Statements.J5P2ConvexLatticeOccupancy

/- Independent canonical for the saved convex-lattice radius-doubling occupancy theorem.
   All dimensions and real radii are retained; no arbitrary-center-family claim. -/
noncomputable section
open Set Metric

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Lattice (d : ℕ) := Fin d → ℤ

def embed {d : ℕ} (z : Lattice d) : E d :=
  WithLp.toLp 2 (fun j => (z j : ℝ))

abbrev statement : Prop :=
  ∀ {d : ℕ} (C : Set (E d)) (hC : Convex ℝ C)
      (hfinite : {z : Lattice d | embed z ∈ C}.Finite) (r : ℝ) (k : ℕ)
      (hthin : ∀ p : E d,
        {z : Lattice d | embed z ∈ C ∧ p ∈ closedBall (embed z) r}.ncard ≤ k)
      (x : E d),
      {z : Lattice d | embed z ∈ C ∧ embed z ∈ closedBall x (2 * r)}.ncard ≤ 2 ^ d * k

end
end Statements.J5P2ConvexLatticeOccupancy

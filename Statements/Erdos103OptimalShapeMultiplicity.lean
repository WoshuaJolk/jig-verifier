import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Isometry

namespace Statements.Erdos103OptimalShapeMultiplicity

abbrev Point := EuclideanSpace ℝ (Fin 2)

def OneSeparated (X : Finset Point) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y

def Optimal (n : ℕ) (X : Finset Point) : Prop :=
  X.card = n ∧ OneSeparated X ∧
    ∀ Y : Finset Point, Y.card = n → OneSeparated Y →
      Metric.diam (X : Set Point) ≤ Metric.diam (Y : Set Point)

def Congruent (X Y : Finset Point) : Prop :=
  ∃ e : Point ≃ᵢ Point, ∀ x : Point, x ∈ X ↔ e x ∈ Y

/-- Erdős Problem 103: the number of congruence classes of
diameter-minimising one-separated planar n-point sets tends to infinity. -/
abbrev statement : Prop :=
  ∀ k : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
    ∃ X : Fin k → Finset Point,
      (∀ i, Optimal n (X i)) ∧
      ∀ i j, i ≠ j → ¬Congruent (X i) (X j)

theorem target : statement := sorry

end Statements.Erdos103OptimalShapeMultiplicity

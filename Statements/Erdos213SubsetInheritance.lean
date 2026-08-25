import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card

open EuclideanGeometry

namespace Statements.Erdos213SubsetInheritance

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsGeneralPosition (S : Set Point) : Prop :=
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 3 → ¬ Collinear ℝ Q) ∧
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 4 → ¬ Cospherical Q)

def HasIntegralDistances (S : Set Point) : Prop :=
  S.Pairwise fun p q => dist p q ∈ Set.range Int.cast

def ExistsConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Point, S.Finite ∧ S.ncard = n ∧
    IsGeneralPosition S ∧ HasIntegralDistances S

/-- Every subset of an integral general-position configuration
is again such a configuration. -/
abbrev statement : Prop :=
  ∀ m n : ℕ, m ≤ n →
    ExistsConfiguration n → ExistsConfiguration m

theorem target : statement := sorry

end Statements.Erdos213SubsetInheritance

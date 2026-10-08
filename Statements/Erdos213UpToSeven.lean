import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card

open EuclideanGeometry

namespace Statements.Erdos213UpToSeven

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsGeneralPosition (S : Set Point) : Prop :=
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 3 → ¬ Collinear ℝ Q) ∧
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 4 → ¬ Cospherical Q)

def HasIntegralDistances (S : Set Point) : Prop :=
  S.Pairwise fun p q => dist p q ∈ Set.range Int.cast

def ExistsConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Point,
    S.Finite ∧ S.ncard = n ∧
    IsGeneralPosition S ∧ HasIntegralDistances S

/-- Erdős Problem 213 holds for every size from four through seven:
integral planar point sets in general position of each of these sizes exist. -/
abbrev statement : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 7 → ExistsConfiguration n

theorem target : statement := sorry

end Statements.Erdos213UpToSeven

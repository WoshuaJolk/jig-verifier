import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card

open EuclideanGeometry

namespace Submissions.Erdos213SubsetInheritance.SubsetHereditary

abbrev Point := EuclideanSpace ℝ (Fin 2)

def IsGeneralPosition (S : Set Point) : Prop :=
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 3 → ¬ Collinear ℝ Q) ∧
  (∀ Q : Set Point, Q ⊆ S → Q.ncard = 4 → ¬ Cospherical Q)

def HasIntegralDistances (S : Set Point) : Prop :=
  S.Pairwise fun p q => dist p q ∈ Set.range Int.cast

def ExistsConfiguration (n : ℕ) : Prop :=
  ∃ S : Set Point, S.Finite ∧ S.ncard = n ∧
    IsGeneralPosition S ∧ HasIntegralDistances S

theorem proof : ∀ m n : ℕ, m ≤ n →
    ExistsConfiguration n → ExistsConfiguration m := by
  intro m n hmn ⟨S, hfin, hcard, ⟨h3, h4⟩, hint⟩
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_card_eq (s := S) (n := m) (by omega)
  exact ⟨T, hfin.subset hTS, hT,
    ⟨fun Q hQ hc => h3 Q (hQ.trans hTS) hc, fun Q hQ hc => h4 Q (hQ.trans hTS) hc⟩,
    hint.mono hTS⟩

end Submissions.Erdos213SubsetInheritance.SubsetHereditary

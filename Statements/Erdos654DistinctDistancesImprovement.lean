import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos654DistinctDistancesImprovement

open Filter Finset

abbrev Point := ℝ × ℝ

def distSq (x y : Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

def NoFourCocyclic (P : Finset Point) : Prop :=
  ∀ S : Finset Point, S ⊆ P → S.card = 4 →
    ¬ ∃ o : Point, ∃ r : ℝ, ∀ x ∈ S, distSq o x = r

noncomputable def distanceCount (P : Finset Point) (x : Point) : ℕ := by
  classical
  exact ((P.erase x).image fun y => distSq x y).card

/-- The surviving weaker conjecture in Erdős problem 654. -/
abbrev statement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      ∀ P : Finset Point, P.card = n → NoFourCocyclic P →
        ∃ x ∈ P, (1 / 3 + c) * n < distanceCount P x

theorem target : statement := sorry

end Statements.Erdos654DistinctDistancesImprovement

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Statements.Erdos654OneThirdBaseline

open Finset

abbrev Point := ℝ × ℝ

def distSq (x y : Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

def NoFourCocyclic (P : Finset Point) : Prop :=
  ∀ S : Finset Point, S ⊆ P → S.card = 4 →
    ¬ ∃ o : Point, ∃ r : ℝ, ∀ x ∈ S, distSq o x = r

noncomputable def distanceCount (P : Finset Point) (x : Point) : ℕ := by
  classical
  exact ((P.erase x).image fun y => distSq x y).card

/-- The elementary circle-occupancy argument gives the baseline one-third
bound at every point. -/
abbrev statement : Prop :=
  ∀ P : Finset Point, NoFourCocyclic P →
    ∀ x ∈ P, P.card - 1 ≤ 3 * distanceCount P x

theorem target : statement := sorry

end Statements.Erdos654OneThirdBaseline

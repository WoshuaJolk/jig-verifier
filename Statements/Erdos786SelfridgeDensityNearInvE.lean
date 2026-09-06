import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Statements.Erdos786SelfridgeDensityNearInvE

open Filter
open scoped Topology

noncomputable abbrev partialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  ((((A ∩ Set.univ) ∩ Set.Iio n).ncard : ℕ) : ℝ) /
    ((((Set.univ : Set ℕ) ∩ Set.Iio n).ncard : ℕ) : ℝ)

def HasDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (partialDensity A) atTop (𝓝 δ)

def IsMulCardSet (A : Set ℕ) : Prop :=
  ∀ a b : Finset ℕ, (a : Set ℕ) ⊆ A → (b : Set ℕ) ⊆ A →
    a.prod id = b.prod id → a.card = b.card

/-- Selfridge's construction, distinct-factor form: for every ε > 0 there is a set of
positive integers of natural density above 1/e − ε in which equal products of two
finite sets of distinct elements force equal cardinalities. -/
abbrev statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ A : Set ℕ, ∃ δ : ℝ,
      0 ∉ A ∧ Real.exp (-1) - ε < δ ∧ HasDensity A δ ∧ IsMulCardSet A

theorem target : statement := sorry

end Statements.Erdos786SelfridgeDensityNearInvE

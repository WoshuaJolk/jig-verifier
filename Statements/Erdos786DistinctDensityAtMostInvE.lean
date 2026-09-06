import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Statements.Erdos786DistinctDensityAtMostInvE

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

/-- Sharp negative form of Erdős 786(i) for distinct factors, as reported for Ruzsa
in Erdős–Graham (1980): a set of positive integers in which equal products of two
finite sets of distinct elements force equal cardinalities has natural density at
most 1/e. -/
abbrev statement : Prop :=
  ∀ (A : Set ℕ) (δ : ℝ), 0 ∉ A → HasDensity A δ → IsMulCardSet A → δ ≤ Real.exp (-1)

theorem target : statement := sorry

end Statements.Erdos786DistinctDensityAtMostInvE

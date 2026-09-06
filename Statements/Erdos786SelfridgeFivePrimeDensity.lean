import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.MetricSpace.Basic

namespace Statements.Erdos786SelfridgeFivePrimeDensity

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

/-- A distinct-factor product-length-rigid set of natural density
1622144/5010005 ≈ 0.3238 > 1/4: the Selfridge family on the primes 3, 5, 7, 11, 13,
i.e. the integers divisible exactly once by exactly one of these primes and by none
of the others. -/
abbrev statement : Prop :=
  ∃ A : Set ℕ, 0 ∉ A ∧ HasDensity A (1622144 / 5010005) ∧ IsMulCardSet A

theorem target : statement := sorry

end Statements.Erdos786SelfridgeFivePrimeDensity

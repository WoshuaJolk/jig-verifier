import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Statements.Erdos349GeometricFloorCompleteness

open Filter Finset Set

def subsetSums (A : Set ℤ) : Set ℤ :=
  {z | ∃ B : Finset ℤ, ↑B ⊆ A ∧ z = ∑ b ∈ B, b}

def IsAddComplete (A : Set ℤ) : Prop :=
  ∀ᶠ z : ℤ in atTop, z ∈ subsetSums A

def IsGoodPair (t α : ℝ) : Prop :=
  IsAddComplete (range (fun n : ℕ ↦ ⌊t * α ^ n⌋))

/-- A central open positive region in Erdős Problem 349. -/
abbrev statement : Prop :=
  ∀ t α : ℝ, 0 < t → α ∈ Ioo 1 ((1 + √5) / 2) → IsGoodPair t α

theorem target : statement := sorry

end Statements.Erdos349GeometricFloorCompleteness

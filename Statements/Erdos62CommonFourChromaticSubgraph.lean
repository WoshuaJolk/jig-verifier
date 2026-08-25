import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Aleph

universe u

namespace Statements.Erdos62CommonFourChromaticSubgraph

open Cardinal

def ColorableBy (C : Type u) {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ color : V → C, ∀ ⦃v w⦄, G.Adj v w → color v ≠ color w

def HasChromaticAlephOne {V : Type u} (G : SimpleGraph V) : Prop :=
  ColorableBy (ℵ₁ : Cardinal.{u}).out G ∧
    ¬ColorableBy (ULift.{u} ℕ) G

def HasChromaticFour {V : Type u} (G : SimpleGraph V) : Prop :=
  ColorableBy (ULift.{u} (Fin 4)) G ∧
    ¬ColorableBy (ULift.{u} (Fin 3)) G

def EmbedsInto {W V : Type u} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W ↪ V, ∀ ⦃v w⦄, H.Adj v w → G.Adj (f v) (f w)

/-- Erdős Problem 62: two `ℵ₁`-chromatic graphs have a common
four-chromatic subgraph. -/
abbrev statement : Prop :=
  ∀ (V₁ V₂ : Type u) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticAlephOne G₁ → HasChromaticAlephOne G₂ →
      ∃ (W : Type u) (H : SimpleGraph W),
        HasChromaticFour H ∧ EmbedsInto H G₁ ∧ EmbedsInto H G₂

theorem target : statement := sorry

end Statements.Erdos62CommonFourChromaticSubgraph

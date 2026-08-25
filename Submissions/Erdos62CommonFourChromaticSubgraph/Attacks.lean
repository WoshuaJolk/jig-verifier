import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Tactic

universe u

namespace Submissions.Erdos62CommonFourChromaticSubgraph.Attacks

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

abbrev claimedStatement : Prop :=
  ∀ (V₁ V₂ : Type u) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticAlephOne G₁ → HasChromaticAlephOne G₂ →
      ∃ (W : Type u) (H : SimpleGraph W),
        HasChromaticFour H ∧ EmbedsInto H G₁ ∧ EmbedsInto H G₂

theorem vacuousHypothesis : False → claimedStatement := False.elim

theorem completeAlephOneColorable :
    ColorableBy (ℵ₁ : Cardinal.{u}).out
      (⊤ : SimpleGraph (ℵ₁ : Cardinal.{u}).out) := by
  exact ⟨id, by simp⟩

end Submissions.Erdos62CommonFourChromaticSubgraph.Attacks

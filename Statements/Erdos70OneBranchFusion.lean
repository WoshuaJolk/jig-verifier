import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70OneBranchFusion

def sameAnchorSignature {α : Type*} (F : Finset α)
    (isRed : α → α → α → Prop) (x x' : α) : Prop :=
  ∀ a b : ↥F, isRed x a.1 b.1 ↔ isRed x' a.1 b.1

def redTripleIn {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ isRed x y z

def blueTripleIn {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ ¬ isRed x y z

/-- Every uncountable subfiber still contains both triple colors. Under failure
of the red `ω·2`/blue-four conclusion, this is the mixing property needed by
one-branch fusion. -/
def hereditarilyMixed {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∀ V : Set α, V ⊆ U → ¬ V.Countable →
    redTripleIn V isRed ∧ blueTripleIn V isRed

def splitWitnessInside {α : Type*} (U : Set α) (F : Finset α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
  ∃ x' ∈ U, ∃ y' ∈ U, ∃ z' ∈ U,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' ∧
    sameAnchorSignature F isRed x x' ∧
    sameAnchorSignature F isRed y y' ∧
    sameAnchorSignature F isRed z z' ∧
    ¬ (isRed x y z ↔ isRed x' y' z')

/-- A finite signature partition of an uncountable parent has one
uncountable child. If the parent is hereditarily mixed, that single child
already contains opposite-colored triples giving the next split; several
simultaneously large siblings are unnecessary at the finite stage. -/
abbrev statement : Prop :=
  (∀ {α : Type*} (U : Set α) (F : Finset α)
      (isRed : α → α → α → Prop),
    ¬ U.Countable →
      ∃ V : Set α, V ⊆ U ∧ ¬ V.Countable ∧
      ∃ x ∈ V, ∀ u ∈ V, sameAnchorSignature F isRed u x) ∧
  (∀ {α : Type*} (U : Set α)
      (isRed : α → α → α → Prop),
    ¬ U.Countable → hereditarilyMixed U isRed →
      ∀ F : Finset α, ∃ V : Set α,
        V ⊆ U ∧ ¬ V.Countable ∧
        (∃ x ∈ V, ∀ u ∈ V, sameAnchorSignature F isRed u x) ∧
        splitWitnessInside V F isRed)

theorem target : statement := sorry

end Statements.Erdos70OneBranchFusion

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70HereditaryMixing

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

def blue4 (isRed : (𝔠 : Cardinal.{0}).ord.ToType →
    (𝔠 : Cardinal.{0}).ord.ToType →
    (𝔠 : Cardinal.{0}).ord.ToType → Prop) : Prop :=
  ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
    triplewise s (fun x y z ↦ ¬ isRed x y z)

def redTripleIn {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ isRed x y z

def blueTripleIn {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ ¬ isRed x y z

def hereditarilyMixed {α : Type*} (U : Set α)
    (isRed : α → α → α → Prop) : Prop :=
  ∀ V : Set α, V ⊆ U → ¬ V.Countable →
    redTripleIn V isRed ∧ blueTripleIn V isRed

/-- In a counterexample to the red `ω·2`/blue-four conclusion, every
uncountable vertex subset contains distinct triples of both colors. -/
abbrev statement : Prop :=
  ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop,
    ¬ redOrderCopy (𝔠).ord (ω * 2) isRed →
    ¬ blue4 isRed →
    hereditarilyMixed Set.univ isRed

theorem target : statement := sorry

end Statements.Erdos70HereditaryMixing

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70BlueTwo

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def ramsey3 (α β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧
      (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ triplewise s isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧
      triplewise s (fun x y z ↦ ¬ isRed x y z))

/-- The blue-target-two boundary case of Erdős Problem 70. -/
abbrev statement : Prop :=
  ∀ β : Ordinal.{0}, β.card ≤ ℵ₀ →
    ramsey3 (𝔠).ord β 2

theorem target : statement := sorry

end Statements.Erdos70BlueTwo

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70OmegaTwoLinkObstruction

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def pivotCover {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ isRed x a b → ¬ isRed x a c → ¬ isRed x b c →
    isRed a b c

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

/-- The red graph in the link of `x` has an edge inside `s`. -/
def linkRedEdge {α : Type*} (isRed : α → α → α → Prop)
    (x : α) (s : Set α) : Prop :=
  ∃ y ∈ s, ∃ z ∈ s, y ≠ z ∧ isRed x y z

/-- Under the pivot-cover condition, either the desired red `ω·2` order-copy
already exists, or every pivot-link red graph meets every disjoint `ω·2`
order-copy. Thus a counterexample has an `ω·2`-hitting link at every pivot. -/
abbrev statement : Prop :=
  ∀ isRed : (𝔠).ord.ToType → (𝔠).ord.ToType → (𝔠).ord.ToType → Prop,
    pivotCover isRed →
      redOrderCopy (𝔠).ord (ω * 2) isRed ∨
      ∀ (x : (𝔠).ord.ToType) (s : Set (𝔠).ord.ToType),
        x ∉ s → typeLT s = ω * 2 → linkRedEdge isRed x s

theorem target : statement := sorry

end Statements.Erdos70OmegaTwoLinkObstruction

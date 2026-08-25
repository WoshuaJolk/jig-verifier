import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70FiniteVertexTypes

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

/-- The triple color is determined by finitely many vertex types. -/
def finiteVertexTypes {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∃ k : ℕ, ∃ label : α → Fin k,
    ∃ pattern : Fin k → Fin k → Fin k → Prop,
      ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
        (isRed x y z ↔ pattern (label x) (label y) (label z))

/-- The ambient continuum defeats every finite vertex-type analogue of the
countable two-block counterstructure. A finite partition has an uncountable
fiber; its constant pure triple color yields either an explicitly ordered red
`ω·2` copy or a blue four-set. -/
abbrev statement : Prop :=
  ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop,
    finiteVertexTypes isRed →
      redOrderCopy (𝔠).ord (ω * 2) isRed ∨
      ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
        triplewise s (fun x y z ↦ ¬ isRed x y z)

theorem target : statement := sorry

end Statements.Erdos70FiniteVertexTypes

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70VaryingCutLinksClassification

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

/-- The red graph in the link of pivot `x` is a complete bipartite graph,
with a cut that may depend arbitrarily on `x`. -/
def varyingCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side x y ≠ side x z)

/-- The same complete-bipartite link graph is used at every pivot. -/
def commonCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side y ≠ side z)

/-- Exact cross-pivot coherence collapses even arbitrarily varying
complete-bipartite pivot links. Every distinct triple is blue, each pivot cut
is constant away from its pivot, and the colouring therefore has a common-cut
representation and a blue four-set. -/
abbrev statement : Prop :=
  ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType → (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop)
    (side : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Bool),
    symmetric3 isRed → varyingCutLinks isRed side →
      (∀ x y z, x ≠ y → y ≠ z → x ≠ z → ¬ isRed x y z) ∧
      (∀ x y z, x ≠ y → y ≠ z → x ≠ z → side x y = side x z) ∧
      (∃ commonSide : (𝔠 : Cardinal.{0}).ord.ToType → Bool,
        commonCutLinks isRed commonSide) ∧
      ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
        triplewise s (fun x y z ↦ ¬ isRed x y z)

theorem target : statement := sorry

end Statements.Erdos70VaryingCutLinksClassification

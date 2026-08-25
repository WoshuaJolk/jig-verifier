import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70CoherentCutLinksBlueFour

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

/-- Every pivot link is the same complete bipartite graph defined by `side`. -/
def commonCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side y ≠ side z)

/-- Cross-pivot coherence collapses the complete-bipartite link
counterstructure: if all links use one common cut and come from a symmetric
triple colouring, every distinct triple is blue, hence a blue four-set exists. -/
abbrev statement : Prop :=
  ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType → (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop)
    (side : (𝔠 : Cardinal.{0}).ord.ToType → Bool),
    symmetric3 isRed → commonCutLinks isRed side →
      (∀ x y z, x ≠ y → y ≠ z → x ≠ z → ¬ isRed x y z) ∧
      ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
        triplewise s (fun x y z ↦ ¬ isRed x y z)

theorem target : statement := sorry

end Statements.Erdos70CoherentCutLinksBlueFour

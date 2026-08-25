import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70FiniteAnchorCriterion

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def pivotCover {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ r x a b → ¬ r x a c → ¬ r x b c → r a b c

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

def finiteVertexTypes {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∃ k : ℕ, ∃ label : α → Fin k,
    ∃ pattern : Fin k → Fin k → Fin k → Prop,
      ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
        (isRed x y z ↔ pattern (label x) (label y) (label z))

/-- The finite signature of `x` records all colors using `x` and two anchors. -/
noncomputable def anchorSignature {α : Type*} (A : Finset α)
    (isRed : α → α → α → Prop) (x : α) : (↥A → ↥A → Bool) := by
  classical
  exact fun a b ↦ decide (isRed x a.1 b.1)

def canonicalAt {α : Type*} (A : Finset α)
    (isRed : α → α → α → Prop) : Prop :=
  ∀ x y z x' y' z',
    x ≠ y → y ≠ z → x ≠ z →
    x' ≠ y' → y' ≠ z' → x' ≠ z' →
    anchorSignature A isRed x = anchorSignature A isRed x' →
    anchorSignature A isRed y = anchorSignature A isRed y' →
    anchorSignature A isRed z = anchorSignature A isRed z' →
    (isRed x y z ↔ isRed x' y' z')

def finiteAnchorCanonical {α : Type*}
    (isRed : α → α → α → Prop) : Prop :=
  ∃ A : Finset α, canonicalAt A isRed

def ramseyConclusion
    (isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop) : Prop :=
  redOrderCopy (𝔠).ord (ω * 2) isRed ∨
  ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
    triplewise s (fun x y z ↦ ¬ isRed x y z)

/-- The exact missing combinatorial principle for the anchor-enlargement
strategy: either a finite anchor canonizes the coloring, or the desired Ramsey
conclusion already appears. -/
def anchorSplitPrinciple : Prop :=
  ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop,
    symmetric3 isRed → pivotCover isRed →
      finiteAnchorCanonical isRed ∨ ramseyConclusion isRed

/-- Finite-anchor canonization really does produce finitely many vertex
types. Consequently the named `anchorSplitPrinciple` reduces every symmetric
`pivotCover` coloring to the finite-type case or the desired conclusion. -/
abbrev statement : Prop :=
  (∀ {α : Type*} (isRed : α → α → α → Prop),
    finiteAnchorCanonical isRed → finiteVertexTypes isRed) ∧
  (anchorSplitPrinciple →
    ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop,
      symmetric3 isRed → pivotCover isRed →
        finiteVertexTypes isRed ∨ ramseyConclusion isRed)

theorem target : statement := sorry

end Statements.Erdos70FiniteAnchorCriterion

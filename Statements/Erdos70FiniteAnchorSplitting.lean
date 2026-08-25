import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal Ordinal
open scoped Cardinal

namespace Statements.Erdos70FiniteAnchorSplitting

def sameAnchorSignature {α : Type*} (F : Finset α)
    (isRed : α → α → α → Prop) (x x' : α) : Prop :=
  ∀ a b : ↥F, isRed x a.1 b.1 ↔ isRed x' a.1 b.1

def canonicalAt {α : Type*} (F : Finset α)
    (isRed : α → α → α → Prop) : Prop :=
  ∀ x y z x' y' z',
    x ≠ y → y ≠ z → x ≠ z →
    x' ≠ y' → y' ≠ z' → x' ≠ z' →
    sameAnchorSignature F isRed x x' →
    sameAnchorSignature F isRed y y' →
    sameAnchorSignature F isRed z z' →
    (isRed x y z ↔ isRed x' y' z')

def finiteAnchorCanonical {α : Type*}
    (isRed : α → α → α → Prop) : Prop :=
  ∃ F : Finset α, canonicalAt F isRed

/-- A one-step failure of canonization: two coordinatewise
signature-indistinguishable triples have different colors. -/
def splitWitness {α : Type*} (F : Finset α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x y z x' y' z',
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' ∧
    sameAnchorSignature F isRed x x' ∧
    sameAnchorSignature F isRed y y' ∧
    sameAnchorSignature F isRed z z' ∧
    ¬ (isRed x y z ↔ isRed x' y' z')

/-- Finite-depth recursion obtained by adjoining every witness vertex to the
next anchor. -/
def splitDepth {α : Type*} [DecidableEq α]
    (isRed : α → α → α → Prop) : ℕ → Finset α → Prop
  | 0, _ => True
  | n + 1, F =>
      ∃ x y z x' y' z',
        (x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' ∧
        sameAnchorSignature F isRed x x' ∧
        sameAnchorSignature F isRed y y' ∧
        sameAnchorSignature F isRed z z' ∧
        ¬ (isRed x y z ↔ isRed x' y' z')) ∧
        splitDepth isRed n (insert x <| insert y <| insert z <|
          insert x' <| insert y' <| insert z' F)

/-- The cardinal strengthening not supplied by ordinary noncanonization.
It requires all three paired signature fibers in a split witness to remain
of cardinality continuum. -/
def continuumSplitAt
    (F : Finset (𝔠 : Cardinal.{0}).ord.ToType)
    (isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop) : Prop :=
  ∃ x y z x' y' z',
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' ∧
    sameAnchorSignature F isRed x x' ∧
    sameAnchorSignature F isRed y y' ∧
    sameAnchorSignature F isRed z z' ∧
    ¬ (isRed x y z ↔ isRed x' y' z') ∧
    #{u | sameAnchorSignature F isRed u x} = 𝔠 ∧
    #{u | sameAnchorSignature F isRed u y} = 𝔠 ∧
    #{u | sameAnchorSignature F isRed u z} = 𝔠

/-- Failure of every finite anchor gives a split witness at every anchor, so
the step can be iterated after adjoining each finite witness. It does not by
itself provide the continuum-sized fibers required for a König/Cantor limit
construction; that extra requirement is isolated by `continuumSplitAt`. -/
abbrev statement : Prop :=
  ∀ {α : Type*} (isRed : α → α → α → Prop),
    ¬ finiteAnchorCanonical isRed →
      ∀ F : Finset α, splitWitness F isRed

theorem target : statement := sorry

end Statements.Erdos70FiniteAnchorSplitting

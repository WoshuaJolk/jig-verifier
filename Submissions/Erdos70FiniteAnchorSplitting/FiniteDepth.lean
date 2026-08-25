import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70FiniteAnchorSplitting.FiniteDepth

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

def splitWitness {α : Type*} (F : Finset α)
    (isRed : α → α → α → Prop) : Prop :=
  ∃ x y z x' y' z',
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    x' ≠ y' ∧ y' ≠ z' ∧ x' ≠ z' ∧
    sameAnchorSignature F isRed x x' ∧
    sameAnchorSignature F isRed y y' ∧
    sameAnchorSignature F isRed z z' ∧
    ¬ (isRed x y z ↔ isRed x' y' z')

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

private theorem oneStep {α : Type*} (isRed : α → α → α → Prop)
    (hnoncanonical : ¬ finiteAnchorCanonical isRed)
    (F : Finset α) : splitWitness F isRed := by
  have hfailure : ¬ canonicalAt F isRed := by
    intro hcanonical
    exact hnoncanonical ⟨F, hcanonical⟩
  simp only [canonicalAt] at hfailure
  push_neg at hfailure
  obtain ⟨x, y, z, x', y', z', hxy, hyz, hxz,
    hx'y', hy'z', hx'z', hxSig, hySig, hzSig, hcolor⟩ := hfailure
  refine ⟨x, y, z, x', y', z', hxy, hyz, hxz,
    hx'y', hy'z', hx'z', hxSig, hySig, hzSig, ?_⟩
  tauto

private theorem everyFiniteDepth {α : Type*} [DecidableEq α]
    (isRed : α → α → α → Prop)
    (hnoncanonical : ¬ finiteAnchorCanonical isRed) :
    ∀ n F, splitDepth isRed n F := by
  intro n
  induction n with
  | zero =>
      intro F
      trivial
  | succ n ih =>
      intro F
      obtain ⟨x, y, z, x', y', z', hwitness⟩ :=
        oneStep isRed hnoncanonical F
      refine ⟨x, y, z, x', y', z', hwitness, ?_⟩
      exact ih _

theorem proof :
    ∀ {α : Type*} (isRed : α → α → α → Prop),
      ¬ finiteAnchorCanonical isRed →
        ∀ F : Finset α, splitWitness F isRed := by
  exact fun isRed h F ↦ oneStep isRed h F

end Submissions.Erdos70FiniteAnchorSplitting.FiniteDepth

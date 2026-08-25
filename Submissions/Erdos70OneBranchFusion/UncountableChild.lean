import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70OneBranchFusion.UncountableChild

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

private theorem uncountableSignatureChild {α : Type*}
    (U : Set α) (F : Finset α) (isRed : α → α → α → Prop)
    (hU : ¬ U.Countable) :
    ∃ V : Set α, V ⊆ U ∧ ¬ V.Countable ∧
      ∃ x ∈ V, ∀ u ∈ V, sameAnchorSignature F isRed u x := by
  classical
  let Signature := ↥F → ↥F → Bool
  let signature : α → Signature :=
    fun x a b ↦ decide (isRed x a.1 b.1)
  let cell : Signature → Set α :=
    fun s ↦ {x | x ∈ U ∧ signature x = s}
  have hlarge : ∃ s, ¬ (cell s).Countable := by
    by_contra h
    push_neg at h
    have hall : (⋃ s, cell s) = U := by
      ext x
      simp [cell]
    apply hU
    rw [← hall]
    exact Set.countable_iUnion h
  obtain ⟨s, hs⟩ := hlarge
  have hsNonempty : (cell s).Nonempty := by
    by_contra hempty
    push_neg at hempty
    apply hs
    rw [hempty]
    exact Set.countable_empty
  obtain ⟨x, hx⟩ := hsNonempty
  refine ⟨cell s, ?_, hs, x, hx, ?_⟩
  · intro u hu
    exact hu.1
  · intro u hu a b
    have hsignature : signature u = signature x :=
      hu.2.trans hx.2.symm
    have hvalue := congrFun (congrFun hsignature a) b
    exact decide_eq_decide.mp hvalue

private theorem sameSignature_trans {α : Type*} {F : Finset α}
    {isRed : α → α → α → Prop} {x y z : α}
    (hxy : sameAnchorSignature F isRed x y)
    (hzy : sameAnchorSignature F isRed z y) :
    sameAnchorSignature F isRed x z :=
  fun a b ↦ (hxy a b).trans (hzy a b).symm

theorem proof :
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
          splitWitnessInside V F isRed) := by
  refine ⟨fun U F isRed hU ↦ uncountableSignatureChild U F isRed hU, ?_⟩
  intro α U isRed hU hmixed F
  obtain ⟨V, hVU, hV, p, hp, hsignature⟩ :=
    uncountableSignatureChild U F isRed hU
  obtain ⟨hred, hblue⟩ := hmixed V hVU hV
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hxyz⟩ := hred
  obtain ⟨x', hx', y', hy', z', hz', hx'y', hy'z', hx'z', hxyz'⟩ := hblue
  refine ⟨V, hVU, hV, ⟨p, hp, hsignature⟩,
    x, hx, y, hy, z, hz, x', hx', y', hy', z', hz',
    hxy, hyz, hxz, hx'y', hy'z', hx'z', ?_, ?_, ?_, ?_⟩
  · exact sameSignature_trans (hsignature x hx) (hsignature x' hx')
  · exact sameSignature_trans (hsignature y hy) (hsignature y' hy')
  · exact sameSignature_trans (hsignature z hz) (hsignature z' hz')
  · tauto

end Submissions.Erdos70OneBranchFusion.UncountableChild

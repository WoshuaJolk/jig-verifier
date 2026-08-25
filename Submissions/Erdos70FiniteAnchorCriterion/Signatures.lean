import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70FiniteAnchorCriterion.Signatures

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

def anchorSplitPrinciple : Prop :=
  ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType →
      (𝔠 : Cardinal.{0}).ord.ToType → Prop,
    symmetric3 isRed → pivotCover isRed →
      finiteAnchorCanonical isRed ∨ ramseyConclusion isRed

private theorem finiteTypesOfAnchor {α : Type*}
    (isRed : α → α → α → Prop)
    (hanchor : finiteAnchorCanonical isRed) :
    finiteVertexTypes isRed := by
  classical
  obtain ⟨A, hcanon⟩ := hanchor
  let Signature := ↥A → ↥A → Bool
  let e : Signature ≃ Fin (Fintype.card Signature) :=
    Fintype.equivFin Signature
  let label : α → Fin (Fintype.card Signature) :=
    fun x ↦ e (anchorSignature A isRed x)
  let pattern : Fin (Fintype.card Signature) →
      Fin (Fintype.card Signature) →
      Fin (Fintype.card Signature) → Prop :=
    fun i j k ↦ ∃ x y z,
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      label x = i ∧ label y = j ∧ label z = k ∧ isRed x y z
  refine ⟨Fintype.card Signature, label, pattern, ?_⟩
  intro x y z hxy hyz hxz
  constructor
  · intro hred
    exact ⟨x, y, z, hxy, hyz, hxz, rfl, rfl, rfl, hred⟩
  · rintro ⟨x', y', z', hx'y', hy'z', hx'z',
      hxLabel, hyLabel, hzLabel, hred⟩
    have hxSignature :
        anchorSignature A isRed x = anchorSignature A isRed x' := by
      apply e.injective
      simpa only [label] using hxLabel.symm
    have hySignature :
        anchorSignature A isRed y = anchorSignature A isRed y' := by
      apply e.injective
      simpa only [label] using hyLabel.symm
    have hzSignature :
        anchorSignature A isRed z = anchorSignature A isRed z' := by
      apply e.injective
      simpa only [label] using hzLabel.symm
    exact (hcanon x y z x' y' z' hxy hyz hxz
      hx'y' hy'z' hx'z' hxSignature hySignature hzSignature).mpr hred

theorem proof :
    (∀ {α : Type*} (isRed : α → α → α → Prop),
      finiteAnchorCanonical isRed → finiteVertexTypes isRed) ∧
    (anchorSplitPrinciple →
      ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
          (𝔠 : Cardinal.{0}).ord.ToType →
          (𝔠 : Cardinal.{0}).ord.ToType → Prop,
        symmetric3 isRed → pivotCover isRed →
          finiteVertexTypes isRed ∨ ramseyConclusion isRed) := by
  refine ⟨finiteTypesOfAnchor, ?_⟩
  intro hsplit isRed hsym hpivot
  obtain hanchor | hramsey := hsplit isRed hsym hpivot
  · exact Or.inl (finiteTypesOfAnchor isRed hanchor)
  · exact Or.inr hramsey

end Submissions.Erdos70FiniteAnchorCriterion.Signatures

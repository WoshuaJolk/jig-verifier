import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70HereditaryMixing.EveryUncountableSet

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

def blue4 (isRed : (𝔠 : Cardinal.{0}).ord.ToType →
    (𝔠 : Cardinal.{0}).ord.ToType →
    (𝔠 : Cardinal.{0}).ord.ToType → Prop) : Prop :=
  ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
    triplewise s (fun x y z ↦ ¬ isRed x y z)

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

private theorem orderCopyOfType {α β : Ordinal.{0}} {s : Set α.ToType}
    (hs : typeLT s = β) : Nonempty (β.ToType ≃o s) := by
  have htype : typeLT β.ToType = typeLT s := by
    rw [Ordinal.type_toType, hs]
  exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htype))⟩

theorem proof :
    ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop,
      ¬ redOrderCopy (𝔠).ord (ω * 2) isRed →
      ¬ blue4 isRed →
      hereditarilyMixed Set.univ isRed := by
  intro isRed hnoRedCopy hnoBlue4 V _ hV
  have hInfinite : V.Infinite := fun hfin ↦ hV hfin.countable
  letI : Infinite V := hInfinite.to_subtype
  let f : ℕ ↪ V := Infinite.natEmbedding V
  have hf : Function.Injective f := f.injective
  have h01 : (f 0).1 ≠ (f 1).1 := by
    intro h
    exact (by decide : (0 : ℕ) ≠ 1) (hf (Subtype.ext h))
  have h02 : (f 0).1 ≠ (f 2).1 := by
    intro h
    exact (by decide : (0 : ℕ) ≠ 2) (hf (Subtype.ext h))
  have h03 : (f 0).1 ≠ (f 3).1 := by
    intro h
    exact (by decide : (0 : ℕ) ≠ 3) (hf (Subtype.ext h))
  have h12 : (f 1).1 ≠ (f 2).1 := by
    intro h
    exact (by decide : (1 : ℕ) ≠ 2) (hf (Subtype.ext h))
  have h13 : (f 1).1 ≠ (f 3).1 := by
    intro h
    exact (by decide : (1 : ℕ) ≠ 3) (hf (Subtype.ext h))
  have h23 : (f 2).1 ≠ (f 3).1 := by
    intro h
    exact (by decide : (2 : ℕ) ≠ 3) (hf (Subtype.ext h))
  constructor
  · by_contra hnoRedTriple
    apply hnoBlue4
    rw [redTripleIn] at hnoRedTriple
    push_neg at hnoRedTriple
    let s : Set ((𝔠 : Cardinal.{0}).ord.ToType) :=
      {(f 0).1, (f 1).1, (f 2).1, (f 3).1}
    have hsV : s ⊆ V := by
      intro x hx
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · exact (f 0).2
      · exact (f 1).2
      · exact (f 2).2
      · exact (f 3).2
    refine ⟨s, ?_, ?_⟩
    · rw [Cardinal.mk_insert, Cardinal.mk_insert, Cardinal.mk_insert,
        Cardinal.mk_singleton]
      · norm_num
      · simpa only [Set.mem_singleton_iff] using h23
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨h12, h13⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨h01, h02, h03⟩
    · intro x hx y hy z hz hxy hyz hxz
      exact hnoRedTriple x (hsV hx) y (hsV hy) z (hsV hz) hxy hyz hxz
  · by_contra hnoBlueTriple
    apply hnoRedCopy
    rw [blueTripleIn] at hnoBlueTriple
    push_neg at hnoBlueTriple
    have hVCard : ℵ₀ < #V := by
      apply lt_of_not_ge
      intro hle
      exact hV (Cardinal.mk_le_aleph0_iff.mp hle)
    have hβlt : ω * 2 < typeLT V := by
      apply lt_of_not_ge
      intro hle
      have hcard := Ordinal.card_le_card hle
      have hcountβ : (ω * 2 : Ordinal.{0}).card ≤ ℵ₀ := by simp
      have hcountV : (typeLT V).card ≤ ℵ₀ := hcard.trans hcountβ
      rw [Ordinal.card_type] at hcountV
      exact (not_le_of_gt hVCard) hcountV
    let b : V := Ordinal.enum (α := V) (· < ·) ⟨ω * 2, hβlt⟩
    let t : Set V := Set.Iio b
    have ht : typeLT t = ω * 2 := by
      change Ordinal.type (α := Set.Iio b) (· < ·) = ω * 2
      rw [Ordinal.type_Iio_lt]
      dsimp only [b]
      exact Ordinal.typein_enum (α := V) (· < ·) _
    let s : Set ((𝔠 : Cardinal.{0}).ord.ToType) := Subtype.val '' t
    let e : t ≃ s :=
      Equiv.Set.image (fun u : V ↦ u.1) t Subtype.val_injective
    let eo : t ≃o s :=
      { e with
        map_rel_iff' := by
          intro x y
          rfl }
    have htypes : typeLT t = typeLT s :=
      Ordinal.type_eq.mpr ⟨eo.toRelIsoLT⟩
    have hs : typeLT s = ω * 2 := by rw [← htypes, ht]
    refine ⟨s, hs, orderCopyOfType hs, ?_⟩
    intro x hx y hy z hz hxy hyz hxz
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    rcases hz with ⟨z, hz, rfl⟩
    exact hnoBlueTriple x.1 x.2 y.1 y.2 z.1 z.2 hxy hyz hxz

end Submissions.Erdos70HereditaryMixing.EveryUncountableSet

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70FiniteVertexTypes.UncountableFiber

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

def finiteVertexTypes {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∃ k : ℕ, ∃ label : α → Fin k,
    ∃ pattern : Fin k → Fin k → Fin k → Prop,
      ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
        (isRed x y z ↔ pattern (label x) (label y) (label z))

private theorem orderCopyOfType {α β : Ordinal.{0}} {s : Set α.ToType}
    (hs : typeLT s = β) : Nonempty (β.ToType ≃o s) := by
  have htype : typeLT β.ToType = typeLT s := by
    rw [Ordinal.type_toType, hs]
  exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htype))⟩

theorem proof :
    ∀ isRed : (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop,
      finiteVertexTypes isRed →
        redOrderCopy (𝔠).ord (ω * 2) isRed ∨
        ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
          triplewise s (fun x y z ↦ ¬ isRed x y z) := by
  intro isRed hfinite
  obtain ⟨k, label, pattern, hpattern⟩ := hfinite
  let U : Fin k → Set ((𝔠 : Cardinal.{0}).ord.ToType) :=
    fun i ↦ {x | label x = i}
  have hU : ∃ i, ¬ (U i).Countable := by
    by_contra h
    push_neg at h
    have hcount : ∀ i, (U i).Countable := fun i ↦ h i
    have hunion : (⋃ i, U i) = Set.univ := by
      ext x
      simp [U]
    have hall : (Set.univ : Set ((𝔠 : Cardinal.{0}).ord.ToType)).Countable := by
      rw [← hunion]
      exact Set.countable_iUnion hcount
    have htype : Countable ((𝔠 : Cardinal.{0}).ord.ToType) :=
      Set.countable_univ_iff.mp hall
    have hmk : #((𝔠 : Cardinal.{0}).ord.ToType) ≤ ℵ₀ :=
      Cardinal.mk_le_aleph0_iff.mpr htype
    rw [Cardinal.mk_ord_toType] at hmk
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hmk
  obtain ⟨i, hi⟩ := hU
  have hiCard : ℵ₀ < #(U i) := by
    apply lt_of_not_ge
    intro hle
    exact hi (Cardinal.mk_le_aleph0_iff.mp hle)
  classical
  by_cases hpure : pattern i i i
  · apply Or.inl
    have hβlt : ω * 2 < typeLT (U i) := by
      apply lt_of_not_ge
      intro hle
      have hcard := Ordinal.card_le_card hle
      have hcountβ : (ω * 2 : Ordinal.{0}).card ≤ ℵ₀ := by simp
      have hcountU : (typeLT (U i)).card ≤ ℵ₀ :=
        hcard.trans hcountβ
      rw [Ordinal.card_type] at hcountU
      exact (not_le_of_gt hiCard) hcountU
    let b : U i :=
      Ordinal.enum (α := U i) (· < ·) ⟨ω * 2, hβlt⟩
    let t : Set (U i) := Set.Iio b
    have ht : typeLT t = ω * 2 := by
      change Ordinal.type (α := Set.Iio b) (· < ·) = ω * 2
      rw [Ordinal.type_Iio_lt]
      dsimp only [b]
      exact Ordinal.typein_enum (α := U i) (· < ·) _
    let s : Set ((𝔠 : Cardinal.{0}).ord.ToType) :=
      Subtype.val '' t
    let e : t ≃ s :=
      Equiv.Set.image (fun u : U i ↦ u.1) t Subtype.val_injective
    let eo : t ≃o s :=
      { e with
        map_rel_iff' := by
          intro x y
          rfl }
    have htypes : typeLT t = typeLT s :=
      Ordinal.type_eq.mpr ⟨eo.toRelIsoLT⟩
    have hs : typeLT s = ω * 2 := by
      rw [← htypes, ht]
    refine ⟨s, hs, orderCopyOfType hs, ?_⟩
    intro x hx y hy z hz hxy hyz hxz
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    rcases hz with ⟨z, hz, rfl⟩
    apply (hpattern x.1 y.1 z.1 hxy hyz hxz).mpr
    have hxLabel : label x.1 = i := by
      change label x.1 = i
      exact x.2
    have hyLabel : label y.1 = i := by
      change label y.1 = i
      exact y.2
    have hzLabel : label z.1 = i := by
      change label z.1 = i
      exact z.2
    rw [hxLabel, hyLabel, hzLabel]
    exact hpure
  · apply Or.inr
    have hiInfinite : (U i).Infinite := fun hfin ↦ hi hfin.countable
    letI : Infinite (U i) := hiInfinite.to_subtype
    let f : ℕ ↪ U i := Infinite.natEmbedding (U i)
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
    have hblue {x y z : (𝔠 : Cardinal.{0}).ord.ToType}
        (hx : x ∈ U i) (hy : y ∈ U i) (hz : z ∈ U i)
        (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
        ¬ isRed x y z := by
      intro hred
      apply hpure
      have hp := (hpattern x y z hxy hyz hxz).mp hred
      have hxLabel : label x = i := by
        change label x = i
        exact hx
      have hyLabel : label y = i := by
        change label y = i
        exact hy
      have hzLabel : label z = i := by
        change label z = i
        exact hz
      rw [hxLabel, hyLabel, hzLabel] at hp
      exact hp
    let s : Set ((𝔠 : Cardinal.{0}).ord.ToType) :=
      {(f 0).1, (f 1).1, (f 2).1, (f 3).1}
    have hsU : s ⊆ U i := by
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
      exact hblue (hsU hx) (hsU hy) (hsU hz) hxy hyz hxz

end Submissions.Erdos70FiniteVertexTypes.UncountableFiber

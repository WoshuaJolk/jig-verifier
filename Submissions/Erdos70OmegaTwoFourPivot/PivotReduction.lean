import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70OmegaTwoFourPivot.PivotReduction

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def ramsey3 (α β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    symmetric3 isRed →
    (∃ s : Set α.ToType, typeLT s = β ∧ triplewise s isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧
      triplewise s (fun x y z ↦ ¬ isRed x y z))

def pivotCover {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ isRed x a b → ¬ isRed x a c → ¬ isRed x b c →
    isRed a b c

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

private theorem orderCopyOfType {α : Ordinal.{0}}
    {β : Ordinal.{0}} {s : Set α.ToType}
    (hs : typeLT s = β) : Nonempty (β.ToType ≃o s) := by
  have htype : typeLT β.ToType = typeLT s := by
    rw [Ordinal.type_toType, hs]
  exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htype))⟩

private theorem permuteNot {α : Type*} {isRed : α → α → α → Prop}
    (hsym : symmetric3 isRed) {x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h : ¬ isRed x y z) :
    ¬ isRed x y z ∧ ¬ isRed y x z ∧ ¬ isRed x z y ∧
      ¬ isRed z x y ∧ ¬ isRed y z x ∧ ¬ isRed z y x := by
  have hyxz : ¬ isRed y x z := by
    intro h'
    exact h ((hsym x y z hxy hyz hxz).1.mpr h')
  have hxzy : ¬ isRed x z y := by
    intro h'
    exact h ((hsym x y z hxy hyz hxz).2.mpr h')
  have hzxy : ¬ isRed z x y := by
    intro h'
    exact hxzy ((hsym x z y hxz hyz.symm hxy).1.mpr h')
  have hyzx : ¬ isRed y z x := by
    intro h'
    exact hyxz ((hsym y x z hxy.symm hxz hyz).2.mpr h')
  have hzyx : ¬ isRed z y x := by
    intro h'
    exact hzxy ((hsym z x y hxz.symm hxy hyz.symm).2.mpr h')
  exact ⟨h, hyxz, hxzy, hzxy, hyzx, hzyx⟩

theorem proof :
    ramsey3 (𝔠).ord (ω * 2) 4 ↔
      ∀ isRed, symmetric3 isRed → pivotCover isRed →
        redOrderCopy (𝔠).ord (ω * 2) isRed := by
  constructor
  · intro hramsey isRed hsym hpivot
    obtain ⟨s, hs, hred⟩ | ⟨s, hs, hblue⟩ := hramsey isRed hsym
    · exact ⟨s, hs, orderCopyOfType hs, hred⟩
    · obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hs
      let f : Fin 4 → (𝔠).ord.ToType := fun i ↦ (e.symm i).1
      have hf : Function.Injective f :=
        Subtype.val_injective.comp e.symm.injective
      have hmem (i : Fin 4) : f i ∈ s := (e.symm i).2
      have h01 : f 0 ≠ f 1 := by
        intro h
        have := hf h
        norm_num at this
      have h02 : f 0 ≠ f 2 := by
        intro h
        have := hf h
        exact (by decide : (0 : Fin 4) ≠ 2) this
      have h03 : f 0 ≠ f 3 := by
        intro h
        have := hf h
        exact (by decide : (0 : Fin 4) ≠ 3) this
      have h12 : f 1 ≠ f 2 := by
        intro h
        have := hf h
        exact (by decide : (1 : Fin 4) ≠ 2) this
      have h13 : f 1 ≠ f 3 := by
        intro h
        have := hf h
        exact (by decide : (1 : Fin 4) ≠ 3) this
      have h23 : f 2 ≠ f 3 := by
        intro h
        have := hf h
        exact (by decide : (2 : Fin 4) ≠ 3) this
      have h012 : ¬ isRed (f 0) (f 1) (f 2) :=
        hblue (hmem 0) (hmem 1) (hmem 2) h01 h12 h02
      have h013 : ¬ isRed (f 0) (f 1) (f 3) :=
        hblue (hmem 0) (hmem 1) (hmem 3) h01 h13 h03
      have h023 : ¬ isRed (f 0) (f 2) (f 3) :=
        hblue (hmem 0) (hmem 2) (hmem 3) h02 h23 h03
      have h123 : ¬ isRed (f 1) (f 2) (f 3) :=
        hblue (hmem 1) (hmem 2) (hmem 3) h12 h23 h13
      exact (h123 (hpivot (f 0) (f 1) (f 2) (f 3)
        h01 h02 h03 h12 h13 h23 h012 h013 h023)).elim
  · intro hreduction isRed hsym
    classical
    by_cases hpivot : pivotCover isRed
    · obtain ⟨s, hs, _, hred⟩ := hreduction isRed hsym hpivot
      exact Or.inl ⟨s, hs, hred⟩
    · simp only [pivotCover] at hpivot
      push_neg at hpivot
      obtain ⟨x, a, b, c, hxa, hxb, hxc, hab, hac, hbc,
        hxab, hxac, hxbc, habc⟩ := hpivot
      obtain ⟨hxab, haxb, hxba, hbxa, habx, hbax⟩ :=
        permuteNot hsym hxa hab hxb hxab
      obtain ⟨hxac, haxc, hxca, hcxa, hacx, hcax⟩ :=
        permuteNot hsym hxa hac hxc hxac
      obtain ⟨hxbc, hbxc, hxcb, hcxb, hbcx, hcbx⟩ :=
        permuteNot hsym hxb hbc hxc hxbc
      obtain ⟨habc, hbac, hacb, hcab, hbca, hcba⟩ :=
        permuteNot hsym hab hbc hac habc
      refine Or.inr ⟨{x, a, b, c}, ?_, ?_⟩
      · rw [Cardinal.mk_insert, Cardinal.mk_insert, Cardinal.mk_insert,
          Cardinal.mk_singleton]
        · norm_num
        · simpa only [Set.mem_singleton_iff] using hbc
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hab, hac⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hxa, hxb, hxc⟩
      · intro p hp q hq r hr hpq hqr hpr
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq hr
        rcases hp with (rfl | rfl | rfl | rfl) <;>
          rcases hq with (rfl | rfl | rfl | rfl) <;>
          rcases hr with (rfl | rfl | rfl | rfl) <;>
          first | contradiction | assumption

end Submissions.Erdos70OmegaTwoFourPivot.PivotReduction

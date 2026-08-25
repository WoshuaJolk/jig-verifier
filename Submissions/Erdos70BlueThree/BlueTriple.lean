import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70BlueThree.BlueTriple

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def ramsey3 (α β : Ordinal.{0}) (c : Cardinal.{0}) : Prop :=
  ∀ (isRed : α.ToType → α.ToType → α.ToType → Prop),
    (∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      (isRed x y z ↔ isRed y x z) ∧
      (isRed x y z ↔ isRed x z y)) →
    (∃ s : Set α.ToType, typeLT s = β ∧ triplewise s isRed) ∨
    (∃ s : Set α.ToType, #s = c ∧
      triplewise s (fun x y z ↦ ¬ isRed x y z))

theorem proof :
    ∀ β : Ordinal.{0}, β.card ≤ ℵ₀ →
      ramsey3 (𝔠).ord β 3 := by
  intro β hβ isRed hsym
  have hβlt : β < (𝔠).ord :=
    Cardinal.lt_ord.2 (hβ.trans_lt Cardinal.aleph0_lt_continuum)
  classical
  by_cases hall : ∀ x y z : (𝔠).ord.ToType,
      x ≠ y → y ≠ z → x ≠ z → isRed x y z
  · let b : (𝔠).ord.ToType := Ordinal.ToType.mk ⟨β, hβlt⟩
    refine Or.inl ⟨Set.Iio b, ?_, ?_⟩
    · change Ordinal.type (α := Set.Iio b) (· < ·) = β
      rw [Ordinal.type_Iio_lt]
      dsimp only [b, Ordinal.ToType.mk]
      apply Ordinal.typein_enum
    · intro x hx y hy z hz hxy hyz hxz
      exact hall x y z hxy hyz hxz
  · push_neg at hall
    obtain ⟨x, y, z, hxy, hyz, hxz, hxyz⟩ := hall
    have hyxz : ¬isRed y x z := by
      intro h
      exact hxyz ((hsym x y z hxy hyz hxz).1.mpr h)
    have hxzy : ¬isRed x z y := by
      intro h
      exact hxyz ((hsym x y z hxy hyz hxz).2.mpr h)
    have hzxy : ¬isRed z x y := by
      intro h
      exact hxzy ((hsym x z y hxz hyz.symm hxy).1.mpr h)
    have hyzx : ¬isRed y z x := by
      intro h
      exact hyxz ((hsym y x z hxy.symm hxz hyz).2.mpr h)
    have hzyx : ¬isRed z y x := by
      intro h
      exact hzxy ((hsym z x y hxz.symm hxy hyz.symm).2.mpr h)
    refine Or.inr ⟨{x, y, z}, ?_, ?_⟩
    · rw [Cardinal.mk_insert, Cardinal.mk_insert, Cardinal.mk_singleton]
      · norm_num
      · simpa only [Set.mem_singleton_iff] using hyz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxy, hxz⟩
    · intro a ha b hb c hc hab hbc hac
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
      rcases ha with (rfl | rfl | rfl) <;>
        rcases hb with (rfl | rfl | rfl) <;>
        rcases hc with (rfl | rfl | rfl) <;>
        first | contradiction | assumption

end Submissions.Erdos70BlueThree.BlueTriple

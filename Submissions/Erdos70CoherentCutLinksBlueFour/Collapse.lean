import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70CoherentCutLinksBlueFour.Collapse

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def commonCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side y ≠ side z)

private theorem bool_eq_of_ne_iff_ne {a b c : Bool}
    (h : (b ≠ c) ↔ (a ≠ c)) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

theorem proof :
    ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType → (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop)
      (side : (𝔠 : Cardinal.{0}).ord.ToType → Bool),
      symmetric3 isRed → commonCutLinks isRed side →
        (∀ x y z, x ≠ y → y ≠ z → x ≠ z → ¬ isRed x y z) ∧
        ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
          triplewise s (fun x y z ↦ ¬ isRed x y z) := by
  intro isRed side hsym hcut
  have hside {x y z : (𝔠).ord.ToType}
      (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
      side x = side y := by
    apply bool_eq_of_ne_iff_ne
    exact (hcut x y z hxy hyz hxz).symm.trans <|
      ((hsym x y z hxy hyz hxz).1.trans
        (hcut y x z hxy.symm hxz hyz))
  have hallBlue {x y z : (𝔠).ord.ToType}
      (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
      ¬ isRed x y z := by
    intro hred
    have hside_yz : side y = side z :=
      hside hyz hxz.symm hxy.symm
    exact ((hcut x y z hxy hyz hxz).mp hred) hside_yz
  refine ⟨fun _ _ _ hxy hyz hxz ↦ hallBlue hxy hyz hxz, ?_⟩
  have hcard : ℵ₀ ≤ #((𝔠).ord.ToType) := by
    rw [Cardinal.mk_ord_toType]
    exact Cardinal.aleph0_le_continuum
  letI : Infinite ((𝔠).ord.ToType) :=
    Cardinal.aleph0_le_mk_iff.mp hcard
  let f : ℕ ↪ (𝔠).ord.ToType :=
    Infinite.natEmbedding ((𝔠).ord.ToType)
  have hf : Function.Injective f := f.injective
  have h01 : f 0 ≠ f 1 := fun h ↦ (by decide : (0 : ℕ) ≠ 1) (hf h)
  have h02 : f 0 ≠ f 2 := fun h ↦ (by decide : (0 : ℕ) ≠ 2) (hf h)
  have h03 : f 0 ≠ f 3 := fun h ↦ (by decide : (0 : ℕ) ≠ 3) (hf h)
  have h12 : f 1 ≠ f 2 := fun h ↦ (by decide : (1 : ℕ) ≠ 2) (hf h)
  have h13 : f 1 ≠ f 3 := fun h ↦ (by decide : (1 : ℕ) ≠ 3) (hf h)
  have h23 : f 2 ≠ f 3 := fun h ↦ (by decide : (2 : ℕ) ≠ 3) (hf h)
  refine ⟨{f 0, f 1, f 2, f 3}, ?_, ?_⟩
  · rw [Cardinal.mk_insert, Cardinal.mk_insert, Cardinal.mk_insert,
      Cardinal.mk_singleton]
    · norm_num
    · simpa only [Set.mem_singleton_iff] using h23
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, h13⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h01, h02, h03⟩
  · intro x hx y hy z hz hxy hyz hxz
    exact hallBlue hxy hyz hxz

end Submissions.Erdos70CoherentCutLinksBlueFour.Collapse

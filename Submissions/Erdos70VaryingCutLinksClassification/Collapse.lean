import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70VaryingCutLinksClassification.Collapse

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def varyingCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side x y ≠ side x z)

def commonCutLinks {α : Type*} (isRed : α → α → α → Prop)
    (side : α → Bool) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (isRed x y z ↔ side y ≠ side z)

private theorem bool_ne_iff_not_ne_of_ne {a b c : Bool} (hab : a ≠ b) :
    (a ≠ c ↔ ¬ b ≠ c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

private theorem cutOpposite {α : Type*}
    {isRed : α → α → α → Prop} {side : α → α → Bool}
    (hcut : varyingCutLinks isRed side)
    {p a b c : α} (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hred : isRed p a b) :
    (isRed p a c ↔ ¬ isRed p b c) := by
  have hside : side p a ≠ side p b :=
    (hcut p a b hpa hab hpb).mp hred
  calc
    isRed p a c ↔ side p a ≠ side p c :=
      hcut p a c hpa hac hpc
    _ ↔ ¬ side p b ≠ side p c :=
      bool_ne_iff_not_ne_of_ne hside
    _ ↔ ¬ isRed p b c :=
      not_congr (hcut p b c hpb hbc hpc).symm

private theorem fourPointBlue {α : Type*}
    {isRed : α → α → α → Prop} {side : α → α → Bool}
    (hsym : symmetric3 isRed) (hcut : varyingCutLinks isRed side)
    {x y z w : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    ¬ isRed x y z := by
  intro hA
  have hBswap : isRed x y w ↔ isRed y x w :=
    (hsym x y w hxy hyw hxw).1
  have hCswap : isRed x z w ↔ isRed z x w :=
    (hsym x z w hxz hzw hxw).1
  have hDswap : isRed y z w ↔ isRed z y w :=
    (hsym y z w hyz hzw hyw).1
  have hA_y : isRed y x z :=
    (hsym x y z hxy hyz hxz).1.mp hA
  have hA_z : isRed z x y := by
    have hxzy : isRed x z y :=
      (hsym x y z hxy hyz hxz).2.mp hA
    exact (hsym x z y hxz hyz.symm hxy).1.mp hxzy
  have hBC : isRed x y w ↔ ¬ isRed x z w :=
    cutOpposite hcut hxy hxz hxw hyz hyw hzw hA
  have hBD : isRed x y w ↔ ¬ isRed y z w :=
    hBswap.trans <|
      cutOpposite hcut hxy.symm hyz hyw hxz hxw hzw hA_y
  have hCD : isRed x z w ↔ ¬ isRed y z w :=
    hCswap.trans <| (cutOpposite hcut hxz.symm hyz.symm hzw
      hxy hxw hyw hA_z).trans (not_congr hDswap.symm)
  by_cases hB : isRed x y w
  · have hnC : ¬ isRed x z w := hBC.mp hB
    have hnD : ¬ isRed y z w := hBD.mp hB
    exact hnC (hCD.mpr hnD)
  · have hC : isRed x z w := by
      by_contra hnC
      exact hB (hBC.mpr hnC)
    have hnD : ¬ isRed y z w := hCD.mp hC
    exact hB (hBD.mpr hnD)

theorem proof :
    ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType → (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop)
      (side : (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Bool),
      symmetric3 isRed → varyingCutLinks isRed side →
        (∀ x y z, x ≠ y → y ≠ z → x ≠ z → ¬ isRed x y z) ∧
        (∀ x y z, x ≠ y → y ≠ z → x ≠ z → side x y = side x z) ∧
        (∃ commonSide : (𝔠 : Cardinal.{0}).ord.ToType → Bool,
          commonCutLinks isRed commonSide) ∧
        ∃ s : Set (𝔠 : Cardinal.{0}).ord.ToType, #s = 4 ∧
          triplewise s (fun x y z ↦ ¬ isRed x y z) := by
  intro isRed side hsym hcut
  have hcard : ℵ₀ ≤ #((𝔠).ord.ToType) := by
    rw [Cardinal.mk_ord_toType]
    exact Cardinal.aleph0_le_continuum
  letI : Infinite ((𝔠).ord.ToType) :=
    Cardinal.aleph0_le_mk_iff.mp hcard
  have hallBlue {x y z : (𝔠).ord.ToType}
      (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
      ¬ isRed x y z := by
    have hfinite : ({x, y, z} : Set ((𝔠).ord.ToType)).Finite := Set.toFinite _
    obtain ⟨w, hw⟩ := hfinite.exists_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
    exact fourPointBlue hsym hcut hxy hxz (fun h ↦ hw.1 h.symm) hyz
      (fun h ↦ hw.2.1 h.symm) (fun h ↦ hw.2.2 h.symm)
  refine ⟨fun _ _ _ hxy hyz hxz ↦ hallBlue hxy hyz hxz, ?_, ?_, ?_⟩
  · intro x y z hxy hyz hxz
    apply not_ne_iff.mp
    intro hside
    exact hallBlue hxy hyz hxz ((hcut x y z hxy hyz hxz).mpr hside)
  · refine ⟨fun _ ↦ false, ?_⟩
    intro x y z hxy hyz hxz
    constructor
    · exact fun hred ↦ (hallBlue hxy hyz hxz hred).elim
    · simp
  · let f : ℕ ↪ (𝔠).ord.ToType :=
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

end Submissions.Erdos70VaryingCutLinksClassification.Collapse

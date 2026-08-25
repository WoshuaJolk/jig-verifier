import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70BlueTwo.BluePair

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
      ramsey3 (𝔠).ord β 2 := by
  intro β hβ isRed hsym
  have hcard : (1 : Cardinal) < #((𝔠).ord.ToType) := by
    rw [Cardinal.mk_ord_toType]
    exact Cardinal.nat_lt_continuum 1
  letI : Nontrivial ((𝔠).ord.ToType) :=
    Cardinal.one_lt_iff_nontrivial.mp hcard
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ((𝔠).ord.ToType)
  refine Or.inr ⟨{x, y}, ?_, ?_⟩
  · rw [Cardinal.mk_insert (by simpa using hxy), Cardinal.mk_singleton]
    norm_num
  · intro a ha b hb c hc hab hbc hac
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
    rcases ha with rfl | rfl <;>
      rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> contradiction

end Submissions.Erdos70BlueTwo.BluePair

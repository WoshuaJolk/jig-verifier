import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70OmegaTwoLinkObstruction.LinkHitting

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

def pivotCover {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ isRed x a b → ¬ isRed x a c → ¬ isRed x b c →
    isRed a b c

def redOrderCopy (α β : Ordinal.{0})
    (isRed : α.ToType → α.ToType → α.ToType → Prop) : Prop :=
  ∃ s : Set α.ToType,
    typeLT s = β ∧ Nonempty (β.ToType ≃o s) ∧ triplewise s isRed

def linkRedEdge {α : Type*} (isRed : α → α → α → Prop)
    (x : α) (s : Set α) : Prop :=
  ∃ y ∈ s, ∃ z ∈ s, y ≠ z ∧ isRed x y z

private theorem orderCopyOfType {α β : Ordinal.{0}} {s : Set α.ToType}
    (hs : typeLT s = β) : Nonempty (β.ToType ≃o s) := by
  have htype : typeLT β.ToType = typeLT s := by
    rw [Ordinal.type_toType, hs]
  exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp htype))⟩

theorem proof :
    ∀ isRed : (𝔠).ord.ToType → (𝔠).ord.ToType → (𝔠).ord.ToType → Prop,
      pivotCover isRed →
        redOrderCopy (𝔠).ord (ω * 2) isRed ∨
        ∀ (x : (𝔠).ord.ToType) (s : Set (𝔠).ord.ToType),
          x ∉ s → typeLT s = ω * 2 → linkRedEdge isRed x s := by
  intro isRed hpivot
  classical
  by_cases hcopy : redOrderCopy (𝔠).ord (ω * 2) isRed
  · exact Or.inl hcopy
  · refine Or.inr ?_
    intro x s hxs hs
    by_contra hedge
    apply hcopy
    refine ⟨s, hs, orderCopyOfType hs, ?_⟩
    intro a ha b hb c hc hab hbc hac
    apply hpivot x a b c
    · exact fun h ↦ hxs (h ▸ ha)
    · exact fun h ↦ hxs (h ▸ hb)
    · exact fun h ↦ hxs (h ▸ hc)
    · exact hab
    · exact hac
    · exact hbc
    · intro h
      apply hedge
      exact ⟨a, ha, b, hb, hab, h⟩
    · intro h
      apply hedge
      exact ⟨a, ha, c, hc, hac, h⟩
    · intro h
      apply hedge
      exact ⟨b, hb, c, hc, hbc, h⟩

end Submissions.Erdos70OmegaTwoLinkObstruction.LinkHitting

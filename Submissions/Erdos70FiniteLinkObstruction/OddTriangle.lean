import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70FiniteLinkObstruction.OddTriangle

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def pivotCover {α : Type*} (isRed : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ isRed x a b → ¬ isRed x a c → ¬ isRed x b c →
    isRed a b c

def forbiddenColors (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨
  (¬ p ∧ ¬ q ∧ r) ∨ (p ∧ q ∧ r)

def linkForbidden {α : Type*} (isRed : α → α → α → Prop)
    (x a b c : α) : Prop :=
  forbiddenColors (isRed x a b) (isRed x a c) (isRed x b c)

private theorem cutCharacterization (p q r : Prop) :
    (∃ u v w : Bool,
      (p ↔ u ≠ v) ∧ (q ↔ u ≠ w) ∧ (r ↔ v ≠ w)) ↔
      ¬ forbiddenColors p q r := by
  constructor
  · rintro ⟨u, v, w, hp, hq, hr⟩
    fin_cases u <;> fin_cases v <;> fin_cases w <;>
      simp_all [forbiddenColors]
  · intro h
    by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
      simp_all [forbiddenColors]

private theorem nonblueHasForbidden {p q r s : Prop}
    (h : p ∨ q ∨ r ∨ s) :
    forbiddenColors p q r ∨ forbiddenColors p q s ∨
    forbiddenColors p r s ∨ forbiddenColors q r s := by
  by_cases hp : p <;> by_cases hq : q <;>
    by_cases hr : r <;> by_cases hs : s <;>
    simp_all [forbiddenColors]

private theorem forbidden_congr {p p' q q' r r' : Prop}
    (hp : p ↔ p') (hq : q ↔ q') (hr : r ↔ r') :
    forbiddenColors p q r ↔ forbiddenColors p' q' r' := by
  unfold forbiddenColors
  tauto

private theorem rotateIff {α : Type*} {isRed : α → α → α → Prop}
    (hsym : symmetric3 isRed) {x y z : α}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    isRed z x y ↔ isRed x y z := by
  exact ((hsym x y z hxy hyz hxz).2.trans
    (hsym x z y hxz hyz.symm hxy).1).symm

theorem proof :
    (∀ p q r : Prop,
      (∃ u v w : Bool,
        (p ↔ u ≠ v) ∧ (q ↔ u ≠ w) ∧ (r ↔ v ≠ w)) ↔
        ¬ forbiddenColors p q r) ∧
    ∀ (isRed : (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType →
        (𝔠 : Cardinal.{0}).ord.ToType → Prop),
      symmetric3 isRed → pivotCover isRed →
      ∀ x a b c, x ≠ a → x ≠ b → x ≠ c →
        a ≠ b → a ≠ c → b ≠ c →
        linkForbidden isRed x a b c ∨
        linkForbidden isRed a x b c ∨
        linkForbidden isRed b x a c ∨
        linkForbidden isRed c x a b := by
  refine ⟨cutCharacterization, ?_⟩
  intro isRed hsym hpivot x a b c hxa hxb hxc hab hac hbc
  let p : Prop := isRed x a b
  let q : Prop := isRed x a c
  let r : Prop := isRed x b c
  let s : Prop := isRed a b c
  have hnonblue : p ∨ q ∨ r ∨ s := by
    by_cases hp : p
    · exact Or.inl hp
    by_cases hq : q
    · exact Or.inr (Or.inl hq)
    by_cases hr : r
    · exact Or.inr (Or.inr (Or.inl hr))
    have hs : s := hpivot x a b c hxa hxb hxc hab hac hbc hp hq hr
    exact Or.inr (Or.inr (Or.inr hs))
  obtain hpqr | hpqs | hprs | hqrs := nonblueHasForbidden hnonblue
  · exact Or.inl hpqr
  · apply Or.inr
    apply Or.inl
    apply (forbidden_congr
      (hsym x a b hxa hab hxb).1.symm
      (hsym x a c hxa hac hxc).1.symm
      Iff.rfl).mpr
    exact hpqs
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    apply (forbidden_congr
      (rotateIff hsym hxa hab hxb)
      (hsym x b c hxb hbc hxc).1.symm
      (hsym a b c hab hbc hac).1.symm).mpr
    exact hprs
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply (forbidden_congr
      (rotateIff hsym hxa hac hxc)
      (rotateIff hsym hxb hbc hxc)
      (rotateIff hsym hab hbc hac)).mpr
    exact hqrs

end Submissions.Erdos70FiniteLinkObstruction.OddTriangle

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70PolarizedOverlapPattern.OneSided

abbrev Vertex := Bool × ℕ

def bluePattern (x y z : Vertex) : Prop :=
  (x.1 = false ∧ y.1 = true ∧ z.1 = true) ∨
  (y.1 = false ∧ x.1 = true ∧ z.1 = true) ∨
  (z.1 = false ∧ x.1 = true ∧ y.1 = true)

def isRed (x y z : Vertex) : Prop := ¬ bluePattern x y z

def symmetric3 {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    (r x y z ↔ r y x z) ∧ (r x y z ↔ r x z y)

def pivotCover {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ x a b c,
    x ≠ a → x ≠ b → x ≠ c → a ≠ b → a ≠ c → b ≠ c →
    ¬ r x a b → ¬ r x a c → ¬ r x b c → r a b c

def forbiddenColors (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨
  (¬ p ∧ ¬ q ∧ r) ∨ (p ∧ q ∧ r)

def linkForbidden (x a b c : Vertex) : Prop :=
  forbiddenColors (isRed x a b) (isRed x a c) (isRed x b c)

def twoBlock (A B : Set ℕ) : Set Vertex :=
  {x | (x.1 = false ∧ x.2 ∈ A) ∨ (x.1 = true ∧ x.2 ∈ B)}

def triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z

theorem proof :
    Ordinal.type (Prod.Lex (· < · : Bool → Bool → Prop)
      (· < · : ℕ → ℕ → Prop)) = ω * 2 ∧
    symmetric3 isRed ∧ pivotCover isRed ∧
    (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ ≠ a₂ → b₁ ≠ b₂ →
      isRed (false, a₁) (false, a₂) (true, b₁) ∧
      isRed (false, a₁) (false, a₂) (true, b₂) ∧
      ¬ isRed (false, a₁) (true, b₁) (true, b₂) ∧
      ¬ isRed (false, a₂) (true, b₁) (true, b₂) ∧
      ¬ linkForbidden (false, a₁) (false, a₂) (true, b₁) (true, b₂) ∧
      ¬ linkForbidden (false, a₂) (false, a₁) (true, b₁) (true, b₂) ∧
      linkForbidden (true, b₁) (false, a₁) (false, a₂) (true, b₂) ∧
      linkForbidden (true, b₂) (false, a₁) (false, a₂) (true, b₁)) ∧
    (∀ A B : Set ℕ, A.Infinite → B.Infinite →
      ¬ triplewise (twoBlock A B) isRed) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ordinal.type_prod_lex]
    simp
  · intro x y z hxy hyz hxz
    rcases x with ⟨x, i⟩
    rcases y with ⟨y, j⟩
    rcases z with ⟨z, k⟩
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      simp [isRed, bluePattern]
  · intro x a b c hxa hxb hxc hab hac hbc hxab hxac hxbc
    rcases x with ⟨x, i⟩
    rcases a with ⟨a, j⟩
    rcases b with ⟨b, k⟩
    rcases c with ⟨c, l⟩
    fin_cases x <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [isRed, bluePattern] at *
  · intro a₁ a₂ b₁ b₂ ha hb
    simp [isRed, bluePattern, linkForbidden, forbiddenColors]
  · intro A B hA hB hhom
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨b, hb⟩ := hB.nonempty
    obtain ⟨c, hc, hcb⟩ := hB.nontrivial.exists_ne b
    have hblue := hhom
      (x := (false, a)) (Or.inl ⟨rfl, ha⟩)
      (y := (true, b)) (Or.inr ⟨rfl, hb⟩)
      (z := (true, c)) (Or.inr ⟨rfl, hc⟩)
      (by simp) (by simpa using hcb.symm) (by simp)
    exact hblue (by simp [isRed, bluePattern])

end Submissions.Erdos70PolarizedOverlapPattern.OneSided

import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

open Cardinal Ordinal
open scoped Cardinal

namespace Submissions.Erdos70LinkHittingBarrier.CrossBlocks

abbrev Vertex := Bool × ℕ

def redLink (_pivot x y : Vertex) : Prop := x.1 ≠ y.1

def twoBlock (A B : Set ℕ) : Set Vertex :=
  {x | (x.1 = false ∧ x.2 ∈ A) ∨ (x.1 = true ∧ x.2 ∈ B)}

def linkRedEdge (pivot : Vertex) (s : Set Vertex) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ redLink pivot x y

def pairwiseOn (s : Set Vertex) (r : Vertex → Vertex → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

theorem proof :
    Ordinal.type (Prod.Lex (· < · : Bool → Bool → Prop)
      (· < · : ℕ → ℕ → Prop)) = ω * 2 ∧
    (∀ pivot A B, A.Infinite → B.Infinite →
      linkRedEdge pivot (twoBlock A B)) ∧
    (∀ pivot A B, A.Infinite → B.Infinite →
      ¬ pairwiseOn (twoBlock A B) (fun x y ↦ ¬ redLink pivot x y)) ∧
    (∀ pivot x y z, x ≠ y → y ≠ z → x ≠ z →
      ¬ (redLink pivot x y ∧ redLink pivot x z ∧ redLink pivot y z)) ∧
    (∃ x y z, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      ¬ (redLink x y z ↔ redLink y x z)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ordinal.type_prod_lex]
    simp
  · intro pivot A B hA hB
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨b, hb⟩ := hB.nonempty
    refine ⟨(false, a), ?_, (true, b), ?_, ?_, ?_⟩
    · exact Or.inl ⟨rfl, ha⟩
    · exact Or.inr ⟨rfl, hb⟩
    · simp
    · simp [redLink]
  · intro pivot A B hA hB hblue
    obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨b, hb⟩ := hB.nonempty
    have h := hblue (x := (false, a)) (Or.inl ⟨rfl, ha⟩)
      (y := (true, b)) (Or.inr ⟨rfl, hb⟩) (by simp)
    exact h (by simp [redLink])
  · intro pivot x y z hxy hyz hxz h
    rcases x with ⟨x, i⟩
    rcases y with ⟨y, j⟩
    rcases z with ⟨z, k⟩
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [redLink] at h
  · refine ⟨(false, 0), (true, 0), (true, 1), ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp [redLink]

end Submissions.Erdos70LinkHittingBarrier.CrossBlocks

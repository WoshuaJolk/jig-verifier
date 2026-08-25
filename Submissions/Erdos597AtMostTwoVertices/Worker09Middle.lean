import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open Cardinal SimpleGraph
open scoped Ordinal

namespace Submissions.Erdos597AtMostTwoVertices.Worker09Middle

noncomputable def omegaOne : Ordinal.{0} := Ordinal.omega 1

noncomputable def source : Ordinal.{0} := omegaOne ^ (2 : ℕ)

noncomputable def redTarget : Ordinal.{0} :=
  omegaOne * Ordinal.omega0

def Symmetric {α : Type*} (color : α → α → Bool) : Prop :=
  ∀ x y, color x y = color y x

def OrdinalGraphPartition {V : Type}
    (α β : Ordinal.{0}) (G : SimpleGraph V) : Prop :=
  ∀ color : α.ToType → α.ToType → Bool,
    Symmetric color →
      (∃ H : Set α.ToType,
        typeLT H = β ∧
          ∀ x ∈ H, ∀ y ∈ H, x ≠ y → color x y = false) ∨
      (∃ copy : V ↪ α.ToType,
        ∀ ⦃x y : V⦄, G.Adj x y → color (copy x) (copy y) = true)

theorem redTarget_le_source : redTarget ≤ source := by
  dsimp [redTarget, source, omegaOne]
  rw [pow_two]
  exact mul_le_mul_right (Ordinal.omega0_le_omega 1) _

theorem singleEdge :
    OrdinalGraphPartition source redTarget (completeGraph Bool) := by
  intro color hsym
  by_cases hblue :
      ∃ x y : source.ToType, x ≠ y ∧ color x y = true
  · right
    rcases hblue with ⟨x, y, hxy, hcolor⟩
    let copy : Bool ↪ source.ToType :=
      ⟨fun b => cond b x y, by
        intro a b hab
        cases a <;> cases b <;> simp_all⟩
    refine ⟨copy, ?_⟩
    intro a b hab
    change color (cond a x y) (cond b x y) = true
    cases a <;> cases b
    · simp_all
    · simpa [copy] using (hsym y x).trans hcolor
    · simpa [copy] using hcolor
    · simp_all
  · left
    let e : redTarget.ToType ≤i source.ToType :=
      (Ordinal.type_le_iff.mp (by
        simpa using redTarget_le_source)).some
    let H : Set source.ToType := Set.range e
    refine ⟨H, ?_, ?_⟩
    · exact
        (e.toOrderEmbedding.orderIso.ordinalType_congr.symm).trans
          (Ordinal.type_toType redTarget)
    · intro x hx y hy hxy
      cases h : color x y with
      | false => rfl
      | true => exact (hblue ⟨x, y, hxy, h⟩).elim

theorem proof :
    ∀ (V : Type) (G : SimpleGraph V),
      #V ≤ 2 →
      OrdinalGraphPartition source redTarget G := by
  intro V G hV color hsym
  have hV' : #V ≤ #Bool := by simpa using hV
  rcases hV' with ⟨e⟩
  rcases singleEdge color hsym with hred | ⟨f, hf⟩
  · exact Or.inl hred
  · right
    refine ⟨e.trans f, ?_⟩
    intro x y hxy
    apply hf
    simpa using e.injective.ne hxy.ne

end Submissions.Erdos597AtMostTwoVertices.Worker09Middle

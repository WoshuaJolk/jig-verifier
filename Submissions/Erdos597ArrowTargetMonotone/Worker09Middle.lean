import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.SetTheory.Ordinal.Arithmetic

open SimpleGraph
open scoped Ordinal

namespace Submissions.Erdos597ArrowTargetMonotone.Worker09Middle

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

theorem proof :
    ∀ (V W : Type) (α β : Ordinal.{0})
      (G : SimpleGraph V) (H : SimpleGraph W),
      H ⊑ G →
      OrdinalGraphPartition α β G →
      OrdinalGraphPartition α β H := by
  intro V W α β G H hHG hG color hsym
  rcases hG color hsym with hred | ⟨f, hf⟩
  · exact Or.inl hred
  · rcases hHG with ⟨e⟩
    right
    refine ⟨e.toEmbedding.trans f, ?_⟩
    intro x y hxy
    exact hf (e.toHom.map_rel hxy)

end Submissions.Erdos597ArrowTargetMonotone.Worker09Middle

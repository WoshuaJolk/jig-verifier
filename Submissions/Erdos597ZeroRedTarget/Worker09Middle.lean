import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open scoped Ordinal

namespace Submissions.Erdos597ZeroRedTarget.Worker09Middle

noncomputable def omegaOne : Ordinal.{0} := Ordinal.omega 1

noncomputable def source : Ordinal.{0} := omegaOne ^ (2 : ℕ)

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
    ∀ (V : Type) (G : SimpleGraph V),
      OrdinalGraphPartition source 0 G := by
  intro V G color _
  left
  exact ⟨∅, by simp, by simp⟩

end Submissions.Erdos597ZeroRedTarget.Worker09Middle

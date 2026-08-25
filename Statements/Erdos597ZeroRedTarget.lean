import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open scoped Ordinal

namespace Statements.Erdos597ZeroRedTarget

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

/-- The zero red target calibrates the graph-arrow definition: the empty set
is a red homogeneous set of order type zero under every coloring. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    OrdinalGraphPartition source 0 G

theorem target : statement := sorry

end Statements.Erdos597ZeroRedTarget

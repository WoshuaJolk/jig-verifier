import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.SetTheory.Ordinal.Arithmetic

open SimpleGraph
open scoped Ordinal

namespace Statements.Erdos597ArrowTargetMonotone

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

/-- The graph target is monotone under non-induced containment: if `H` is a
subgraph-copy of `G`, then the arrow relation for `G` implies that for `H`. -/
abbrev statement : Prop :=
  ∀ (V W : Type) (α β : Ordinal.{0})
    (G : SimpleGraph V) (H : SimpleGraph W),
    H ⊑ G →
    OrdinalGraphPartition α β G →
    OrdinalGraphPartition α β H

theorem target : statement := sorry

end Statements.Erdos597ArrowTargetMonotone

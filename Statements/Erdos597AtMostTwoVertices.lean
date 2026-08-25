import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Set
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

open Cardinal SimpleGraph
open scoped Ordinal

namespace Statements.Erdos597AtMostTwoVertices

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

/-- The finite-target question in Erdős 597 holds for every graph with at
most two vertices. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    #V ≤ 2 →
    OrdinalGraphPartition source redTarget G

theorem target : statement := sorry

end Statements.Erdos597AtMostTwoVertices

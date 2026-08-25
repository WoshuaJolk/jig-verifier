import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card

namespace Statements.Erdos1183ChainPigeonhole

def IsChain {α : Type} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ⊆ B ∨ B ⊆ A

def Monochromatic {α : Type} [DecidableEq α]
    (color : Finset α → Bool) (family : Finset (Finset α)) : Prop :=
  ∃ b : Bool, ∀ A ∈ family, color A = b

def UnionClosed {α : Type} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ∪ B ∈ family

/-- In every two-coloring, at least half of any finite chain is a
monochromatic union-closed subfamily. -/
abbrev statement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ family : Finset (Finset α),
      ∀ color : Finset α → Bool,
        IsChain family →
          ∃ mono : Finset (Finset α),
            mono ⊆ family ∧ Monochromatic color mono ∧
              UnionClosed mono ∧ family.card ≤ 2 * mono.card

theorem target : statement := sorry

end Statements.Erdos1183ChainPigeonhole

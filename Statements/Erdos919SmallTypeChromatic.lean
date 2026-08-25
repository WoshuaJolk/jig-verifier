import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace Statements.Erdos919SmallTypeChromatic

open Cardinal

def ProperColoring {V C : Type} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

def ChromaticAtMost {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ C : Type, #C ≤ κ ∧ ∃ c : V → C, ProperColoring G c

def ChromaticAtLeast {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∀ C : Type, #C < κ → ∀ c : V → C, ¬ProperColoring G c

def ChromaticExactly {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ChromaticAtLeast G κ ∧ ChromaticAtMost G κ

/-- The first, aleph-two, question of Erdős Problem 919. -/
abbrev statement : Prop :=
  ∃ (V : Type) (_ : LinearOrder V) (_ : WellFoundedLT V)
      (G : SimpleGraph V),
    Ordinal.type ((· < ·) : V → V → Prop) =
        (ℵ_ (2 : Ordinal)).ord * (ℵ_ (2 : Ordinal)).ord ∧
    ChromaticExactly G (ℵ_ (2 : Ordinal)) ∧
    ∀ S : Set V,
      Ordinal.type ((· < ·) : S → S → Prop) <
        Ordinal.type ((· < ·) : V → V → Prop) →
      ChromaticAtMost (G.induce S) ℵ₀

theorem target : statement := sorry

end Statements.Erdos919SmallTypeChromatic

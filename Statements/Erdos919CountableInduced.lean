import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Aleph

namespace Statements.Erdos919CountableInduced

open Cardinal

def ProperColoring {V C : Type} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

def ChromaticAtMost {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ C : Type, #C ≤ κ ∧ ∃ c : V → C, ProperColoring G c

/-- Every countable vertex subset induces a countably colorable graph. Thus
the unresolved clause in Problem 919 concerns uncountable smaller order types. -/
abbrev statement : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (S : Set V),
    #S ≤ ℵ₀ → ChromaticAtMost (G.induce S) ℵ₀

theorem target : statement := sorry

end Statements.Erdos919CountableInduced

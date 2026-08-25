import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.SetTheory.Cardinal.Aleph

namespace Submissions.Erdos919CountableInduced.Direct

open Cardinal

def ProperColoring {V C : Type} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w

def ChromaticAtMost {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ C : Type, #C ≤ κ ∧ ∃ c : V → C, ProperColoring G c

theorem proof :
    ∀ (V : Type) (G : SimpleGraph V) (S : Set V),
      #S ≤ ℵ₀ → ChromaticAtMost (G.induce S) ℵ₀ := by
  intro V G S hS
  refine ⟨S, hS, id, ?_⟩
  intro v w hvw
  exact hvw.ne

end Submissions.Erdos919CountableInduced.Direct

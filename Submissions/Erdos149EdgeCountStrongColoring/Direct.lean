import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149EdgeCountStrongColoring.Direct

def strongConflict {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f :=
    e ≠ f ∧
      ((G.lineGraph).Adj e f ∨
        ∃ middle : G.edgeSet,
          (G.lineGraph).Adj e middle ∧ (G.lineGraph).Adj middle f)
  symm := ⟨by
    intro e f h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with hef | ⟨middle, hem, hmf⟩
    · exact Or.inl hef.symm
    · exact Or.inr ⟨middle, hmf.symm, hem.symm⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

def StrongColorable {V : Type*} (G : SimpleGraph V) (colors : ℕ) : Prop :=
  (strongConflict G).Colorable colors

theorem proof :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      StrongColorable G (Nat.card G.edgeSet) := by
  intro n G
  unfold StrongColorable
  letI := Fintype.ofFinite G.edgeSet
  rw [Nat.card_eq_fintype_card]
  exact SimpleGraph.colorable_of_fintype (strongConflict G)

end Submissions.Erdos149EdgeCountStrongColoring.Direct

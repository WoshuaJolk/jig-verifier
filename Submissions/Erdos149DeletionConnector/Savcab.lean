import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Submissions.Erdos149DeletionConnector.Savcab

-- This is the definition in the canonical Jig #274 statement, verbatim.
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

open SimpleGraph

def G : SimpleGraph (Fin 4) :=
  fromEdgeSet {s(0, 1), s(1, 2), s(2, 3)}

def H : SimpleGraph (Fin 4) :=
  fromEdgeSet {s(0, 1), s(2, 3)}

theorem retained_subgraph : H ≤ G := by
  intro v w h
  rcases h with ⟨h, hne⟩
  refine ⟨?_, hne⟩
  change s(v, w) = s(0, 1) ∨ s(v, w) = s(2, 3) at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

instance : DecidableRel G.Adj := by unfold G; infer_instance

instance : DecidableRel H.Adj := by unfold H; infer_instance

instance {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) :
    DecidableRel K.lineGraph.Adj := by
  intro e f
  exact decidable_of_iff
    (e ≠ f ∧ ∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V))
    SimpleGraph.lineGraph_adj_iff_exists.symm

def leftG : G.edgeSet := ⟨s(0, 1), by decide⟩
def middleG : G.edgeSet := ⟨s(1, 2), by decide⟩
def rightG : G.edgeSet := ⟨s(2, 3), by decide⟩
def leftH : H.edgeSet := ⟨s(0, 1), by decide⟩
def rightH : H.edgeSet := ⟨s(2, 3), by decide⟩

theorem conflict_in_G : (strongConflict G).Adj leftG rightG := by
  exact ⟨by decide, Or.inr ⟨middleG, by decide, by decide⟩⟩

theorem no_conflict_in_H : ¬ (strongConflict H).Adj leftH rightH := by
  rintro ⟨_, h | ⟨m, hl, hr⟩⟩
  · exact (by decide : ¬ H.lineGraph.Adj leftH rightH) h
  · have hm := m.property
    simp only [H, edgeSet_fromEdgeSet] at hm
    rcases hm.1 with hm | hm
    · have he : m = leftH := Subtype.ext hm
      exact hl.1 he.symm
    · have he : m = rightH := Subtype.ext hm
      exact hr.1 he

/-- Deleting the connecting edge destroys a conflict between retained edges.
This refutes a deletion-based identification of conflict graphs, not Jig #274. -/
theorem deletion_connector_obstruction :
    H ≤ G ∧
    (leftH.val = leftG.val ∧ rightH.val = rightG.val) ∧
    (strongConflict G).Adj leftG rightG ∧
    ¬ (strongConflict H).Adj leftH rightH :=
  ⟨retained_subgraph, ⟨rfl, rfl⟩, conflict_in_G, no_conflict_in_H⟩


end Submissions.Erdos149DeletionConnector.Savcab

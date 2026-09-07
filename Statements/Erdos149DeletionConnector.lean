import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace Statements.Erdos149DeletionConnector

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

abbrev statement : Prop :=
  H ≤ G ∧
  (leftH.val = leftG.val ∧ rightH.val = rightG.val) ∧
  (strongConflict G).Adj leftG rightG ∧
  ¬ (strongConflict H).Adj leftH rightH

theorem target : statement := sorry

end Statements.Erdos149DeletionConnector

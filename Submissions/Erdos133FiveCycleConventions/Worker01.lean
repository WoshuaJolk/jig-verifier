import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace Submissions.Erdos133FiveCycleConventions.Worker01

open SimpleGraph

def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u

def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

theorem proof :
    IsTriangleFree (cycleGraph 5) ∧ HasDiameterAtMostTwo (cycleGraph 5) := by
  constructor
  · simp only [IsTriangleFree]
    decide
  · simp only [HasDiameterAtMostTwo]
    decide

end Submissions.Erdos133FiveCycleConventions.Worker01

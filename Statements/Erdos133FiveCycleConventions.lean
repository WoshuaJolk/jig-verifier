import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace Statements.Erdos133FiveCycleConventions

open SimpleGraph

def IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u

def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-- The five-cycle simultaneously exercises the triangle-free and
diameter-at-most-two conventions used in the Erdős 133 verifier. -/
abbrev statement : Prop :=
  IsTriangleFree (cycleGraph 5) ∧ HasDiameterAtMostTwo (cycleGraph 5)

theorem target : statement := sorry

end Statements.Erdos133FiveCycleConventions

import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Statements.Erdos595NatGraphTriangleCover

def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- Every graph on the countable vertex type `ℕ` is a countable union of
triangle-free graphs. -/
abbrev statement : Prop :=
  ∀ G : SimpleGraph ℕ, IsCountableUnionOfTriangleFree G

theorem target : statement := sorry

end Statements.Erdos595NatGraphTriangleCover

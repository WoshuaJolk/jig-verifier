import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

namespace Statements.Erdos595UncountableK4FreeGraph

def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-- Erdős Problem 595: an infinite K₄-free graph that cannot be covered by
countably many triangle-free graphs. -/
abbrev statement : Prop :=
  ∃ (V : Type*) (_ : Infinite V) (G : SimpleGraph V),
    G.CliqueFree 4 ∧ ¬IsCountableUnionOfTriangleFree G

theorem target : statement := sorry

end Statements.Erdos595UncountableK4FreeGraph

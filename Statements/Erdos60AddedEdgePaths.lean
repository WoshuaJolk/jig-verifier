import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Four-cycles through an added edge are length-three paths

After adding a nonedge `uv`, labelled `C₄` embeddings rooted by
`0 ↦ u, 1 ↦ v` are in bijection with simple length-three `u`-`v` paths in
the original graph.
-/

open SimpleGraph

namespace Statements.Erdos60AddedEdgePaths

abbrev SimpleThreePaths {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) :=
  {p : Fin n × Fin n //
    G.Adj u p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 v ∧
      p.1 ≠ v ∧ p.2 ≠ u}

abbrev RootedAddedEdgeC4s {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) :=
  {f : (cycleGraph 4).Copy (G ⊔ edge u v) //
    f (0 : Fin 4) = u ∧ f (1 : Fin 4) = v}

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n), u ≠ v → ¬G.Adj u v →
    Nat.card (RootedAddedEdgeC4s G u v) =
      Nat.card (SimpleThreePaths G u v)

theorem target : statement := sorry

end Statements.Erdos60AddedEdgePaths

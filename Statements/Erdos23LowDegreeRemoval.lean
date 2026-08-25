import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23LowDegreeRemoval

open scoped Classical in
/-- Removing a vertex of degree at most two and then extending a bipartization
costs at most `floor(deg(v)/2)` additional deleted edges. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ),
    G.degree v ≤ 2 →
    (∃ H : SimpleGraph V,
      H ≤ G.deleteIncidenceSet v ∧ H.IsBipartite ∧
        ((G.deleteIncidenceSet v).edgeFinset \ H.edgeFinset).card ≤ k) →
    ∃ H' : SimpleGraph V,
      H' ≤ G ∧ H'.IsBipartite ∧
        (G.edgeFinset \ H'.edgeFinset).card ≤ k + G.degree v / 2

theorem target : statement := sorry

end Statements.Erdos23LowDegreeRemoval

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

open SimpleGraph

namespace Statements.Erdos23N2MinimumDegreeRanges

open scoped Classical in
/-- On ten vertices, minimum degree `k = 1,2,3` gives the required bound
through respectively `8,12,16` edges. -/
abbrev statement : Prop :=
  ∀ (V : Type) [Fintype V], Fintype.card V = 10 →
    ∀ (G : SimpleGraph V), G.CliqueFree 3 →
      (((∀ v : V, 1 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 8) ∨
        ((∀ v : V, 2 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 12) ∨
        ((∀ v : V, 3 ≤ G.degree v) ∧ G.edgeFinset.card ≤ 16)) →
          ∃ (H : SimpleGraph V),
            H ≤ G ∧ H.IsBipartite ∧
              (G.edgeFinset \ H.edgeFinset).card ≤ 4

theorem target : statement := sorry

end Statements.Erdos23N2MinimumDegreeRanges

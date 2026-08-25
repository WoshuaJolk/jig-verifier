import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Exact multiplicity of unlabelled four-cycles

Every subgraph isomorphic to `C₄` has exactly eight labelled embeddings:
four choices of a starting vertex and two orientations.
-/

open SimpleGraph

namespace Statements.Erdos60C4Multiplicity

abbrev statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    Nat.card ((cycleGraph 4).Copy G) =
      8 * {H' : G.Subgraph |
        Nonempty (H'.coe ≃g cycleGraph 4)}.ncard

theorem target : statement := sorry

end Statements.Erdos60C4Multiplicity

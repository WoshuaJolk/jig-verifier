import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Statements.Erdos1176UniversalEdgeColors

namespace SimpleGraph

noncomputable def chromaticCardinal.{u} {V : Type u}
    (G : _root_.SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal |
    ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

end SimpleGraph

abbrev statement : Prop :=
  ∀ {V : Type*} (G : _root_.SimpleGraph V),
    SimpleGraph.chromaticCardinal G = aleph 1 →
      ∃ (EColor : Type) (_ : mk EColor = aleph 1)
        (edgeColor : G.edgeSet → EColor),
          ∀ (VColor : Type) (_ : mk VColor ≤ aleph 0)
            (vertexColor : V → VColor),
              ∃ vc : VColor,
                ∀ ec : EColor,
                  ∃ (u v : V) (h : G.Adj u v),
                    vertexColor u = vc ∧
                      vertexColor v = vc ∧
                        edgeColor ⟨s(u, v), h⟩ = ec

theorem target : statement := sorry

end Statements.Erdos1176UniversalEdgeColors

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Statements.Erdos1176WitnessIsSurjective

abbrev statement : Prop :=
  ∀ {V EColor : Type} (G : _root_.SimpleGraph V)
    (edgeColor : G.edgeSet → EColor),
      (∀ (VColor : Type) (_ : mk VColor ≤ aleph 0)
        (vertexColor : V → VColor),
          ∃ vc : VColor,
            ∀ ec : EColor,
              ∃ (u v : V) (h : G.Adj u v),
                vertexColor u = vc ∧
                  vertexColor v = vc ∧
                    edgeColor ⟨s(u, v), h⟩ = ec) →
        Function.Surjective edgeColor

theorem target : statement := sorry

end Statements.Erdos1176WitnessIsSurjective

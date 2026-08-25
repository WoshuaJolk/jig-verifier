import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal

namespace Submissions.Erdos1176WitnessIsSurjective.OneVertexColor

theorem proof :
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
          Function.Surjective edgeColor := by
  intro V EColor G edgeColor h
  obtain ⟨vc, hvc⟩ := h PUnit (by simp) (fun _ ↦ PUnit.unit)
  intro ec
  obtain ⟨u, v, huv, -, -, hedge⟩ := hvc ec
  exact ⟨⟨s(u, v), huv⟩, hedge⟩

end Submissions.Erdos1176WitnessIsSurjective.OneVertexColor

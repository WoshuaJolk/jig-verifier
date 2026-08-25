import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2

namespace Submissions.Erdos617ParameterSpaceInhabited.Direct

theorem proof :
    ∀ r : ℕ, r ≥ 3 →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
        Fintype.card V = r ^ 2 + 1 ∧
        Nonempty (Sym2 V → Fin r) := by
  intro r hr
  refine ⟨Fin (r ^ 2 + 1), inferInstance, inferInstance, ?_, ?_⟩
  · simp
  · exact ⟨fun _ => ⟨0, by omega⟩⟩

end Submissions.Erdos617ParameterSpaceInhabited.Direct

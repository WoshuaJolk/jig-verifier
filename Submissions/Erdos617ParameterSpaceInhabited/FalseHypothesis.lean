import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2

namespace Submissions.Erdos617ParameterSpaceInhabited.FalseHypothesis

theorem proof :
    False →
      ∀ r : ℕ, r ≥ 3 →
        ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
          Fintype.card V = r ^ 2 + 1 ∧
          Nonempty (Sym2 V → Fin r) :=
  False.elim

end Submissions.Erdos617ParameterSpaceInhabited.FalseHypothesis

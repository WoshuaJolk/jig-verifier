import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sym.Sym2

namespace Statements.Erdos617ParameterSpaceInhabited

/-- Every admissible parameter has a vertex type of the required size and at least one total edge-colouring. -/
abbrev statement : Prop :=
  ∀ r : ℕ, r ≥ 3 →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
      Fintype.card V = r ^ 2 + 1 ∧
      Nonempty (Sym2 V → Fin r)

theorem target : statement := sorry

end Statements.Erdos617ParameterSpaceInhabited

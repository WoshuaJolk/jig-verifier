import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1045SixPointExact

/-- Exact maximum over all labelled complex sextuples of diameter at most two.
Repeated points are permitted. This is only the six-point case of #1045. -/
abbrev statement : Prop :=
  IsGreatest
    ((fun z : Fin 6 → ℂ =>
      ∏ i : Fin 6, ∏ j ∈ Finset.univ.filter (fun j : Fin 6 => i < j),
        ‖z i - z j‖ ^ 2) ''
      {z : Fin 6 → ℂ | ∀ i j, ‖z i - z j‖ ≤ 2})
    (64 * (2 * Real.sqrt 3 - 2) ^ 18)

-- Required canonical-statement placeholder; not part of any submitted proof.
theorem target : statement := sorry

end Statements.Erdos1045SixPointExact

import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Statements.Erdos1045SixPointAttain

/-- Attainment half of `Statements.Erdos1045SixPointExact`: the value `64 (2√3 - 2)^18`
is the squared-distance product of some complex sextuple of diameter at most two.
This is literally the first conjunct of the `IsGreatest` there. -/
abbrev statement : Prop :=
  (64 * (2 * Real.sqrt 3 - 2) ^ 18) ∈
    ((fun z : Fin 6 → ℂ =>
      ∏ i : Fin 6, ∏ j ∈ Finset.univ.filter (fun j : Fin 6 => i < j),
        ‖z i - z j‖ ^ 2) ''
      {z : Fin 6 → ℂ | ∀ i j, ‖z i - z j‖ ≤ 2})

theorem target : statement := sorry

end Statements.Erdos1045SixPointAttain

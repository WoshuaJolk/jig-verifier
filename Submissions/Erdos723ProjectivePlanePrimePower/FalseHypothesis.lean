import Mathlib.Algebra.IsPrimePow
import Mathlib.Combinatorics.Configuration

namespace Submissions.Erdos723ProjectivePlanePrimePower.FalseHypothesis

open Configuration

/-- The prime-power conjecture for finite projective planes. -/
abbrev statement : Prop :=
  ∀ {P L : Type} (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
    ∀ plane : ProjectivePlane P L, IsPrimePow plane.order

theorem proof : False → statement := False.elim

end Submissions.Erdos723ProjectivePlanePrimePower.FalseHypothesis

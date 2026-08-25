import Mathlib.Algebra.IsPrimePow
import Mathlib.Combinatorics.Configuration

namespace Statements.Erdos723ProjectivePlanePrimePower

open Configuration

/-- The prime-power conjecture for finite projective planes. -/
abbrev statement : Prop :=
  ∀ {P L : Type} (_ : Membership P L) (_ : Fintype P) (_ : Fintype L),
    ∀ plane : ProjectivePlane P L, IsPrimePow plane.order

theorem target : statement := sorry

end Statements.Erdos723ProjectivePlanePrimePower

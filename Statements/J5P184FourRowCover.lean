import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.NormNum

namespace Statements.J5P184FourRowCover

/-- Exact finite 0,1,2,4-iterate cover bound; no cycle-order assumptions. -/
abbrev statement : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α]
    (e : Equiv α α) (C : Finset α),
    2 * (Finset.univ.filter fun x =>
      x ∈ C ∨ e x ∈ C ∨ e (e x) ∈ C ∨ e (e (e (e x))) ∈ C).card ≤
      Fintype.card α + 3 * C.card

end Statements.J5P184FourRowCover

import Mathlib.Data.Fintype.Card

/-!
# Compatibility of multiple involution exclusions

Independent-set constraints arising only from involution matchings do not
multiply their density losses.  A simultaneous parity orientation can retain
one half of every orbit.
-/

namespace Statements.Erdos12InvolutionCompatibility

abbrev statement : Prop :=
  ∀ {X I : Type} [Fintype X] [DecidableEq X] [Nonempty I]
    (σ : I → X → X) (A : Finset X),
    (∀ i x, σ i (σ i x) = x) →
    (∀ i x, x ∈ A → σ i x ∉ A) →
    2 * A.card ≤ Fintype.card X ∧
      (2 * A.card = Fintype.card X →
        ∀ i x, (x ∈ A ↔ σ i x ∉ A))

theorem target : statement := sorry

end Statements.Erdos12InvolutionCompatibility

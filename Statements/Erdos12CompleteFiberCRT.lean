import Mathlib.Data.Fintype.BigOperators

/-!
# Product density from complete-fiber exclusions

Unlike matching-neighbor involutions, opposite-fiber exclusions multiply
across jointly separating coordinates.
-/

namespace Statements.Erdos12CompleteFiberCRT

abbrev statement : Prop :=
  ∀ {ι X : Type} [DecidableEq ι] [DecidableEq X]
    (I : Finset ι) (m : ι → ℕ) (coord : ι → X → ℕ) (B : Finset X),
    (∀ x ∈ B, ∀ i ∈ I, 0 < coord i x ∧ coord i x < m i) →
    (∀ x ∈ B, ∀ y ∈ B, ∀ i ∈ I,
      coord i x + coord i y = m i → x = y) →
    (∀ x ∈ B, ∀ y ∈ B,
      (∀ i ∈ I, coord i x = coord i y) → x = y) →
    B.card ≤ ∏ i ∈ I, m i / 2

theorem target : statement := sorry

end Statements.Erdos12CompleteFiberCRT

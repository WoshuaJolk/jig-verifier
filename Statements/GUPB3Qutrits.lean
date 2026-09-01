import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Statements.GUPB3Qutrits

/-- There is a genuinely unextendible product basis of 14 states in the
three-qutrit system ℂ³ ⊗ ℂ³ ⊗ ℂ³: fourteen nonzero product vectors
`u i ⊗ w i ⊗ z i`, pairwise orthogonal (the product of the three local inner
products vanishes), such that for every bipartition of the three parties the
orthogonal complement of their span contains no nonzero product vector across
that bipartition. Across bipartition A|BC a product vector is `x ⊗ N` with
`x : ℂ³` and `N` a vector of ℂ³ ⊗ ℂ³ written as a 3×3 array, and similarly
for B|AC and C|AB. -/
abbrev statement : Prop :=
  ∃ u : Fin 14 → Fin 3 → ℂ, ∃ w : Fin 14 → Fin 3 → ℂ, ∃ z : Fin 14 → Fin 3 → ℂ,
    (∀ i, u i ≠ 0) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, z i ≠ 0) ∧
    (∀ i j, i ≠ j →
      (∑ r, star (u i r) * u j r) * (∑ r, star (w i r) * w j r) *
        (∑ r, star (z i r) * z j r) = 0) ∧
    (∀ x : Fin 3 → ℂ, x ≠ 0 → ∀ N : Fin 3 → Fin 3 → ℂ, N ≠ 0 →
      ∃ i, (∑ r, star (u i r) * x r) * (∑ r, ∑ s, star (w i r * z i s) * N r s) ≠ 0) ∧
    (∀ y : Fin 3 → ℂ, y ≠ 0 → ∀ N : Fin 3 → Fin 3 → ℂ, N ≠ 0 →
      ∃ i, (∑ r, star (w i r) * y r) * (∑ r, ∑ s, star (u i r * z i s) * N r s) ≠ 0) ∧
    (∀ t : Fin 3 → ℂ, t ≠ 0 → ∀ N : Fin 3 → Fin 3 → ℂ, N ≠ 0 →
      ∃ i, (∑ r, star (z i r) * t r) * (∑ r, ∑ s, star (u i r * w i s) * N r s) ≠ 0)

/-- The open target. A submission proves `statement` in its own module; the verifier
bridges the two. -/
theorem target : statement := sorry

end Statements.GUPB3Qutrits

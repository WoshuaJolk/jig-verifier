import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic

/-!
# C6PathForcesChord

This is the local obstruction that refutes the proposed seed-existence
statement at `k = 2`.

The cycle `C₆` is connected, 2-regular, and is the union of the two perfect
matchings

    {01, 23, 45}  and  {12, 34, 50}.

The common-neighbour hypothesis in the proposed statement ranges over
`2 ≤ j ≤ k - 1`, so it is vacuous when `k = 2`.

If an exact orthogonal representation of `C₆` in `ℂ²` existed, its vectors on
the path `0 - 1 - 2 - 3` would satisfy the proposition below. But `v₀` and
`v₂` lie in the one-dimensional orthogonal complement of the nonzero vector
`v₁`, so they are proportional. Since `v₂ ⟂ v₃`, this forces `v₀ ⟂ v₃`,
contrary to exactness because `03` is not an edge of `C₆`.
-/

namespace Statements.C6PathForcesChord

open scoped BigOperators

/-- The standard Hermitian pairing, conjugate-linear in its first argument. -/
abbrev pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- No six nonzero vectors in `ℂ²` can satisfy the edge/non-edge requirements
on the path `0 - 1 - 2 - 3` inherited from an exact orthogonal representation
of `C₆`. -/
abbrev statement : Prop :=
  ¬ ∃ v : Fin 6 → Fin 2 → ℂ,
    (∀ i, v i ≠ 0) ∧
    pair (v 1) (v 0) = 0 ∧
    pair (v 1) (v 2) = 0 ∧
    pair (v 2) (v 3) = 0 ∧
    pair (v 0) (v 3) ≠ 0

theorem target : statement := sorry

end Statements.C6PathForcesChord

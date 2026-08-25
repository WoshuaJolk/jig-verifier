import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic

/-!
# UniqueMatchingDeterminant

A square matrix whose nonzero support admits exactly one perfect matching has
nonzero determinant.  This is the bridge from a certified zero pattern to a
rank witness without evaluating any nonzero entries.
-/

namespace Statements.UniqueMatchingDeterminant

abbrev statement : Prop :=
  ∀ (n : Type) (_ : Fintype n) (_ : DecidableEq n)
    (M : Matrix n n ℂ) (σ : Equiv.Perm n),
    (∀ i, M (σ i) i ≠ 0) →
    (∀ τ : Equiv.Perm n, τ ≠ σ → ∃ i, M (τ i) i = 0) →
    M.det ≠ 0

theorem target : statement := sorry

end Statements.UniqueMatchingDeterminant

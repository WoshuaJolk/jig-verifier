import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic

/-!
# AdjugateRealizesInvertibleMap

Every invertible complex matrix is a nonzero scalar multiple of the adjugate
of another invertible matrix.
-/

namespace Statements.AdjugateRealizesInvertibleMap

open Matrix

abbrev statement : Prop :=
  ∀ (k : ℕ) (G : Matrix (Fin k) (Fin k) ℂ), IsUnit G.det →
    ∃ (H : Matrix (Fin k) (Fin k) ℂ) (c : ℂ),
      IsUnit H.det ∧ c ≠ 0 ∧ H.adjugate = c • G

theorem target : statement := sorry

end Statements.AdjugateRealizesInvertibleMap

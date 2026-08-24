import Mathlib.Analysis.Matrix.Order

/-!
# PositiveDefiniteGramFactorization

Every finite positive-definite complex matrix is the Gram matrix of an
invertible complex matrix.
-/

namespace Statements.PositiveDefiniteGramFactorization

open Matrix
open scoped MatrixOrder ComplexOrder

abbrev statement : Prop :=
  ∀ (k : ℕ) (K : Matrix (Fin k) (Fin k) ℂ), K.PosDef →
    ∃ L : Matrix (Fin k) (Fin k) ℂ,
      IsUnit L ∧ K = L.conjTranspose * L

theorem target : statement := sorry

end Statements.PositiveDefiniteGramFactorization

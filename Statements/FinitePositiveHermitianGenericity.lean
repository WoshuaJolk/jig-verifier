import Mathlib

/-!
# FinitePositiveHermitianGenericity

Every finite collection of nonzero complex polynomials in the entries of a
square matrix can be made simultaneously nonzero at one positive-definite
Hermitian matrix.

This is the exact algebraic replacement for the informal positive-cone
Zariski-density step in the elliptic seed theorem.
-/

namespace Statements.FinitePositiveHermitianGenericity

open Matrix MvPolynomial
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder

abbrev MatVar (k : ℕ) := Fin k × Fin k

abbrev statement : Prop :=
  ∀ (k n : ℕ) (p : Fin n → MvPolynomial (MatVar k) ℂ),
    (∀ i, p i ≠ 0) →
    ∃ K : Matrix (Fin k) (Fin k) ℂ,
      K.PosDef ∧
      ∀ i, eval (fun ij => K ij.1 ij.2) (p i) ≠ 0

theorem target : statement := sorry

end Statements.FinitePositiveHermitianGenericity

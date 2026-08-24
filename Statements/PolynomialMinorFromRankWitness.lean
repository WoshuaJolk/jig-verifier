import Mathlib

/-!
# PolynomialMinorFromRankWitness

A full-rank evaluation of polynomial vectors witnesses a nonzero square
coordinate-minor polynomial.
-/

namespace Statements.PolynomialMinorFromRankWitness

open Matrix MvPolynomial

abbrev statement : Prop :=
  ∀ (k d : ℕ) (σ : Type) (v : Fin d → Fin k → MvPolynomial σ ℂ)
    (z : σ → ℂ),
    LinearIndependent ℂ (fun q i => eval z (v q i)) →
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => v q (e p)) ≠ 0

theorem target : statement := sorry

end Statements.PolynomialMinorFromRankWitness

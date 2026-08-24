import Mathlib

/-!
# MixedMinorAdjugateBridge

An invertible mixed-rank witness forces a nonzero coordinate-minor polynomial
in the entries of a universal adjugate matrix.
-/

namespace Statements.MixedMinorAdjugateBridge

open Matrix MvPolynomial

noncomputable section

abbrev MatVar (k : ℕ) := Fin k × Fin k

def universalMat {k : ℕ} :
    Matrix (Fin k) (Fin k) (MvPolynomial (MatVar k) ℂ) :=
  fun i j => X (i, j)

def mixedPolyVec {k d : ℕ} (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (q : Fin d) :
    Fin k → MvPolynomial (MatVar k) ℂ :=
  if move q then
    (universalMat (k := k)).adjugate.mulVec (fun i => C (v q i))
  else fun i => C (v q i)

abbrev statement : Prop :=
  ∀ (k d : ℕ) (move : Fin d → Prop) [DecidablePred move]
    (v : Fin d → Fin k → ℂ) (G : Matrix (Fin k) (Fin k) ℂ),
    IsUnit G.det →
    LinearIndependent ℂ
      (fun q => if move q then G.mulVec (v q) else v q) →
    ∃ e : Fin d → Fin k, Function.Injective e ∧
      Matrix.det (Matrix.of fun p q => mixedPolyVec move v q (e p)) ≠ 0

theorem target : statement := sorry

end

end Statements.MixedMinorAdjugateBridge

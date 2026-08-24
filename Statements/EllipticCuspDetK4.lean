import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic

/-!
# EllipticCuspDetK4

The first nontrivial Tate-cusp flattening in the elliptic seed construction.
For `k=4`, the balanced divisor has initial tensor

`(x-z)(x-ωz)(xz-λ)(xz-λω²)`.

After nodal clutching, its genuine four-dimensional flattening has the matrix
below and determinant

`-λ⁴ ω³ (ω-1)² (ω²+ω+1)`.

It is therefore invertible whenever `λ,ω ≠ 0`, `ω ≠ 1`, and `ω³ ≠ 1`.
-/

namespace Statements.EllipticCuspDetK4

def cuspMatrix (lam omega : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![
    ![0, lam^2 * omega^2, 0, 0],
    ![-lam^2 * omega^3 - lam^2 * omega^2, 0,
      -lam * omega^2 - lam, 0],
    ![0, lam * omega^3 + lam * omega^2 + lam * omega + lam, 0, 1],
    ![-lam * omega^3 - lam * omega, 0, -omega - 1, 0]
  ]

abbrev statement : Prop :=
  ∀ lam omega : ℂ,
    (cuspMatrix lam omega).det =
      -lam^4 * omega^3 * (omega - 1)^2 * (omega^2 + omega + 1)

theorem target : statement := sorry

end Statements.EllipticCuspDetK4

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Length4NestedFiberNonvanishing — the first nested cofactor still sees tightness

Length 2 (s=49): on the fibre `W = r^⊥ ∩ n^⊥` of a link, the leading coefficient of the
closing polynomial vanishes identically iff both side vertices lie in `n^⊥`. Tightness
forbids that alternative (`SeedLocalObstruction`).

At the first genuinely new step the next even-chain vertex is forced from *two*
s-dependent predecessors: `x(s)` in the fibre and `y(s) = H(x(s), p, q)`. The s²
coefficient is the Hermitian nested form

  `f(b) = pair (H(b, H(b,p,q), τ), r)`

on `W`. The holomorphic bilinear analogue of `f` *does* vanish identically on a
tightness-compatible configuration (an isotropic `τ_W` for the Euclidean volume).
That invariant is therefore not length-uniform, and the extra hypothesis it would
need is exactly the Hermitian pairing the sequential construction already uses.

In a Hermitian orthonormal frame with the link as the first two axes, `f` is not
the zero form on `W` as soon as `{p,q,n}` and `{r,n,τ}` are independent and not
both `p,q` lie in `r^⊥`. The last hypothesis is the nondegeneracy of the first
cofactor (otherwise `H(x,p,q) ∥ r` on `W` and the forced vertex is parallel to the
root). All three are supplied by tightness plus the sequential pattern: the third
predecessor `τ` is not in the link plane, and at least one side vertex of the first
cofactor is outside `N(r)`.

Nothing is claimed at nesting depth ≥ 2 (chain length ≥ 6), nor about a fixed
unlucky fibre direction — only that `f` is not identically zero on the fibre.
-/

namespace Statements.Length4NestedFiberNonvanishing

open scoped BigOperators
open Matrix

/-- Hermitian pairing, conjugate-linear in the first slot. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- Bilinear 4-dimensional cofactor: `bilinCof u v w` is the unique (up to the
standard volume) vector with `(bilinCof u v w) · x = det(u,v,w,x)`. -/
def bilinCof (u v w : Fin 4 → ℂ) : Fin 4 → ℂ := fun i =>
  (-1 : ℂ) ^ (i : ℕ) *
    Matrix.det (fun a b : Fin 3 => (![u, v, w] b) (i.succAbove a))

/-- Hermitian cofactor, conjugate of the bilinear cofactor. -/
def hermCof (u v w : Fin 4 → ℂ) : Fin 4 → ℂ :=
  star (bilinCof u v w)

def rVec : Fin 4 → ℂ := ![1, 0, 0, 0]
def nVec : Fin 4 → ℂ := ![0, 1, 0, 0]

/-- Nested leading coefficient along a fibre direction, in the link frame
`r = e₀`, `n = e₁`. -/
def nestedLead (b p q tau : Fin 4 → ℂ) : ℂ :=
  pair (hermCof b (hermCof b p q) tau) rVec

/-- In the Hermitian orthonormal link frame, the first nested leading coefficient
is not identically zero on the fibre. -/
abbrev statement : Prop :=
  ∀ (p q tau : Fin 4 → ℂ),
    LinearIndependent ℂ ![p, q, nVec] →
    LinearIndependent ℂ ![rVec, nVec, tau] →
    ¬ (pair rVec p = 0 ∧ pair rVec q = 0) →
    ∃ b : Fin 4 → ℂ,
      pair rVec b = 0 ∧ pair nVec b = 0 ∧ nestedLead b p q tau ≠ 0

theorem target : statement := sorry

end Statements.Length4NestedFiberNonvanishing

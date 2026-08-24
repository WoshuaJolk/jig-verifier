import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Length2FiberNonvanishing — D₂ is not identically zero on the length-2 fibre

In the sequential construction of a 4-dimensional seed, a length-2 chain starts at a root
`r` with a link neighbour `n`. The fibre of the first chain vertex is the Hermitian
2-space `W = r^⊥ ∩ n^⊥`. The next vertex is forced as the cofactor of that fibre vector
against two already-placed side vertices `p, q`. The leading closing coefficient `D₂`
vanishes at a fibre direction `b ∈ W` exactly when `{b, p, q, r}` is linearly dependent.

That vanishing is **identical** on `W` if and only if both side vertices lie in `n^⊥`.
Under exact orthogonality that means both are neighbours of `n`. Combined with the fibre
vertex `x ∈ W`, the forced vertex then shares three common Hermitian neighbours with `n`,
which tightness forbids (`SeedLocalObstruction` at `k = 4`, the `K_{2,3}` case). So in
every tight sequential length-2 configuration there is a fibre direction with `D₂ ≠ 0`:
the length-2 closing polynomial is non-constant.

The identity does not mention the graph, tightness, or a particular 1-parameter subgroup.
Those are how the hypotheses are supplied; the linear algebra is the remaining analytic
input at length 2. Nothing is claimed at nesting depth ≥ 2, and nothing is claimed about
a fixed unlucky direction — only that the form on the whole fibre is not identically zero
unless the side vertices are both orthogonal to the link neighbour.
-/

namespace Statements.Length2FiberNonvanishing

open scoped BigOperators

/-- Hermitian pairing, conjugate-linear in the first slot. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The length-2 fibre form vanishes identically if and only if both side vertices
are Hermitian-orthogonal to the link neighbour. -/
abbrev statement : Prop :=
  ∀ (r n p q : Fin 4 → ℂ),
    LinearIndependent ℂ ![r, n] →
    pair r n = 0 →
    LinearIndependent ℂ ![p, q, r] →
    ((∃ b : Fin 4 → ℂ,
        pair r b = 0 ∧ pair n b = 0 ∧ LinearIndependent ℂ ![b, p, q, r]) ↔
      ¬ (pair n p = 0 ∧ pair n q = 0))

theorem target : statement := sorry

end Statements.Length2FiberNonvanishing

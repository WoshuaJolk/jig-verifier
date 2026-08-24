import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# SeedLocalObstruction — common neighbours of a small set kill tightness

A seed in `C^k` is tight: every set of at most `k - 1` vectors is linearly independent.
That single hypothesis already forbids a local configuration. If a set `T` of `j` vertices
with `2 ≤ j ≤ k - 1` has `k - j + 1` common Hermitian neighbours, those neighbours lie in
the Hermitian orthogonal complement of `span(T)`, a subspace of dimension at most `k - j`,
and are therefore a linearly dependent set of size `k - j + 1 ≤ k - 1`, contradicting tightness.

At `k = 4` the two cases are a pair with three common neighbours and a triple with two;
both are the bipartite graph `K_{2,3}`. So `K_{2,3}`-freeness of the orthogonality graph is
necessary for a 4-dimensional seed. The bound is sharp: an orthonormal basis of `C^k`
is tight and gives a `j`-set exactly `k - j` common neighbours, never one more.

The argument uses only tightness, not connectedness, regularity, or `(k+1)`-spanning, so it
applies to every seed on this board and to every degenerate class the classification still
needs. It is the same dimension count as the easy direction of Lovász–Saks–Schrijver, stated
for an arbitrary `j`-set rather than a single vertex.

Nothing is claimed about existence of seeds, about grouping, or about the closing determinant.
-/

namespace Statements.SeedLocalObstruction

open scoped BigOperators

/-- Hermitian pairing on `Fin k → ℂ`, conjugate-linear in the first slot. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- Tightness in the seed sense: every set of at most `k - 1` vectors is linearly independent. -/
def Tight {k m : ℕ} (v : Fin m → Fin k → ℂ) : Prop :=
  ∀ S : Finset (Fin m), S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i

/-- A tight family in `C^k` (`k ≥ 2`) cannot give `k - j + 1` common Hermitian neighbours
to any `j`-set with `2 ≤ j ≤ k - 1`. -/
abbrev statement : Prop :=
  ∀ (k m : ℕ) (v : Fin m → Fin k → ℂ),
    2 ≤ k →
    Tight v →
    ∀ j : ℕ, 2 ≤ j → j + 1 ≤ k →
      ∀ T : Finset (Fin m), T.card = j →
        ¬ ∃ U : Finset (Fin m),
            U.card = k + 1 - j ∧
            ∀ u ∈ U, ∀ t ∈ T, pair (v u) (v t) = 0

theorem target : statement := sorry

end Statements.SeedLocalObstruction

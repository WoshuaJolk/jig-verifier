import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# NoBipartiteSeedAt2kPlus2

There is no `k`-regular bipartite orthogonality incidence on two parts of
size `k+1` in `ℂ^k` when either part spans. Each vertex omits exactly one
opposite point; regularity makes every co-singleton occur. Those co-singletons
would all have to be proper polar hyperplanes, making a spanning family of
`k+1` vectors irredundant and therefore linearly independent in dimension
`k`, a contradiction.

Consequently a tight `(k+1)`-spanning seed can never use a bipartite graph at
the first admissible even size `m=2k+2`. This rules out an infinite natural
class of connected, automatically one-factorable seed graphs.
-/

namespace Statements.NoBipartiteSeedAt2kPlus2

def localSpan {k n : ℕ} (a : Fin n → EuclideanSpace ℂ (Fin k))
    (S : Finset (Fin n)) : Submodule ℂ (EuclideanSpace ℂ (Fin k)) :=
  Submodule.span ℂ (Set.range fun i : (S : Set (Fin n)) => a i.1)

/-- A spanning side of size `k+1` cannot participate in a `k`-regular
bipartite orthogonality incidence with another nonzero side. -/
abbrev statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∀ a b : Fin (k + 1) → EuclideanSpace ℂ (Fin k),
      (∀ i, b i ≠ 0) →
      localSpan a Finset.univ = ⊤ →
      (∀ i, (Finset.univ.filter fun j => inner ℂ (b i) (a j) = 0).card = k) →
      (∀ j, (Finset.univ.filter fun i => inner ℂ (b i) (a j) = 0).card = k) →
      False

theorem target : statement := sorry

end Statements.NoBipartiteSeedAt2kPlus2

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# SeedNeighborhoodCircuitHyperplane

In a tight exact `k`-regular orthogonal representation in `ℂ^k`, every
neighborhood is not merely a dependent `k`-set. Its span is exactly the
Hermitian polar hyperplane of the corresponding vertex, it contains exactly
that vertex's neighbors, and the neighborhood is a circuit. Thus every seed
determines a complex-representable sparse-paving configuration equipped with a
positive Hermitian polarity.
-/

namespace Statements.SeedNeighborhoodCircuitHyperplane

/-- Tightness: every set of at most `k-1` represented vertices is independent. -/
def Tight {k m : ℕ} (v : Fin m → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ S : Finset (Fin m), S.card + 1 ≤ k →
    LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i.1

/-- The span of the represented vectors indexed by `S`. -/
def localSpan {k m : ℕ} (v : Fin m → EuclideanSpace ℂ (Fin k))
    (S : Finset (Fin m)) : Submodule ℂ (EuclideanSpace ℂ (Fin k)) :=
  Submodule.span ℂ (Set.range fun i : (S : Set (Fin m)) => v i.1)

/-- Every neighborhood is its vertex's exact polar circuit-hyperplane. -/
abbrev statement : Prop :=
  ∀ (k m : ℕ), 2 ≤ k →
    ∀ (v : Fin m → EuclideanSpace ℂ (Fin k))
      (N : Fin m → Finset (Fin m)),
      (∀ i, v i ≠ 0) →
      Tight v →
      (∀ i j, inner ℂ (v i) (v j) = 0 ↔ j ∈ N i) →
      (∀ i, (N i).card = k) →
      ∀ i,
        localSpan v (N i) = (ℂ ∙ v i)ᗮ ∧
        (∀ j, v j ∈ localSpan v (N i) ↔ j ∈ N i) ∧
        ¬ LinearIndependent ℂ
            (fun j : (N i : Set (Fin m)) => v j.1)

theorem target : statement := sorry

end Statements.SeedNeighborhoodCircuitHyperplane

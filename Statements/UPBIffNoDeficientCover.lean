import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Span.Basic

/-!
# UPBIffNoDeficientCover

An orthogonal product family is unextendible exactly when its states cannot be
covered by one locally nonspanning set per tensor factor. This is the exact
matroid-cover formulation behind the killing-number sufficient condition:
killing numbers replace the nonspanning sets by cardinality bounds, but the
cover obstruction itself is necessary and sufficient.
-/

namespace Statements.UPBIffNoDeficientCover

open scoped BigOperators ComplexConjugate

/-- The vectors indexed by `S` in local factor `j` fail to span that factor. -/
def Deficient {p m : ℕ} {d : Fin p → ℕ}
    (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j)))
    (j : Fin p) (S : Finset (Fin m)) : Prop :=
  Submodule.span ℂ
    (Set.range fun i : (S : Set (Fin m)) => v i.1 j) ≠ ⊤

/-- The selected local index sets cover all product states. -/
def Covers {p m : ℕ} (S : (j : Fin p) → Finset (Fin m)) : Prop :=
  ∀ i, ∃ j, i ∈ S j

/-- No nonzero product vector is orthogonal to every state. -/
def Unextendible {p m : ℕ} {d : Fin p → ℕ}
    (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j))) : Prop :=
  ∀ a : (j : Fin p) → EuclideanSpace ℂ (Fin (d j)), (∀ j, a j ≠ 0) →
    ∃ i, ∀ j, inner ℂ (v i j) (a j) ≠ 0

/-- Exact deficient-cover characterization of unextendibility. -/
abbrev statement : Prop :=
  ∀ (p m : ℕ) (d : Fin p → ℕ)
    (v : Fin m → (j : Fin p) → EuclideanSpace ℂ (Fin (d j))),
    Unextendible v ↔
      ¬ ∃ S : (j : Fin p) → Finset (Fin m),
          Covers S ∧ ∀ j, Deficient v j (S j)

theorem target : statement := sorry

end Statements.UPBIffNoDeficientCover

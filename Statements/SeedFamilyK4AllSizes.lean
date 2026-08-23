import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Statements.SeedFamilyK4AllSizes

/-- Hermitian pairing. -/
def pair {k : ℕ} (x y : Fin k → ℂ) : ℂ := ∑ r, star (x r) * y r

/-- The orthogonality graph of a family. -/
def orthGraph {k m : ℕ} (v : Fin m → Fin k → ℂ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i i' => pair (v i) (v i') = 0

/-- A connected `4`-regular tight `5`-spanning family of `m` nonzero vectors in `ℂ⁴`:
the `k = 4` case of the seed hypothesis, with no graph prescribed. -/
abbrev statement : Prop :=
  ∀ m : ℕ, 10 ≤ m →
    ∃ v : Fin m → Fin 4 → ℂ, ∃ N : Fin m → Finset (Fin m),
      (∀ i, v i ≠ 0) ∧
      (∀ i i', pair (v i) (v i') = 0 ↔ i' ∈ N i) ∧
      (∀ i, (N i).card = 4) ∧
      (orthGraph v).Connected ∧
      (∀ S : Finset (Fin m), S.card ≤ 3 →
        LinearIndependent ℂ fun i : (S : Set (Fin m)) => v i) ∧
      (∀ S : Finset (Fin m), S.card = 5 → ∀ a : Fin 4 → ℂ, a ≠ 0 →
        ∃ i ∈ S, pair a (v i) ≠ 0)

theorem target : statement := sorry

end Statements.SeedFamilyK4AllSizes
